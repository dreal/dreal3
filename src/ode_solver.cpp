//solver for ODEs

#include "ode_solver.h"
#include <boost/algorithm/string/join.hpp>
#include <limits>

using namespace capd;

ode_solver::ode_solver(set < variable* > & ode_vars) :
    _ode_vars(ode_vars)
{
}

ode_solver::~ode_solver()
{

}


string ode_solver::create_diffsys_string(set < variable* > & ode_vars,
                                         vector<variable*> & _0_vars,
                                         vector<variable*> & _t_vars)
{
    vector<string> var_list;
    vector<string> ode_list;

    // 1. partition ode_vars into _0_vars and _t_vars by their ODE_vartype
    for(set< variable* >::iterator ite = ode_vars.begin();
        ite != ode_vars.end();
        ite++)
    {
        cerr << (*ite)->getName() << " = ["
             << (*ite)->get_top_lb()
             << ", "
             << (*ite)->get_top_ub()
             << "]" << endl;
        if ((*ite)->get_enode()->getODEvartype() == l_True) {
            _t_vars.push_back(*ite);
        }
        else if ((*ite)->get_enode()->getODEvartype() == l_False) {
            _0_vars.push_back(*ite);
            var_list.push_back((*ite)->get_enode()->getODEvarname());
            ode_list.push_back((*ite)->get_enode()->getODE());
        }
    }

    // 2. Sort _0_vars and _t_vars
    sort(_0_vars.begin(), _0_vars.end());
    sort(_t_vars.begin(), _t_vars.end());

    // 3. join var_list to make diff_var, ode_list to diff_fun
    string diff_var = "var:" + boost::algorithm::join(var_list, ", ") + ";";
    string diff_fun = "fun:" + boost::algorithm::join(ode_list, ", ") + ";";

    // 4. construct diff_sys (string to CAPD)
    cerr << "diff_var : " << diff_var << endl;
    cerr << "diff_fun : " << diff_fun << endl;
    string diff_sys = diff_var + diff_fun;
    cerr << "diff_sys : " << diff_sys << endl;

    return diff_sys;
}


IVector ode_solver::varlist_to_IVector(vector<variable*> vars)
{
    IVector ret (vars.size());

    /* Assign current interval values */
    int i = 0;
    for (vector<variable*>::iterator var_ite = vars.begin();
         var_ite != vars.end();
         var_ite++, i++)
    {
        double lb, ub;
        lb = (*var_ite)->get_top_lb();
        ub = (*var_ite)->get_top_ub();
        ret[i] = interval(lb, ub);
        cout << "The interval on "
             << (*var_ite)->getName()
             << " is "<< ret[i] <<endl;
    }

    return ret;
}

void ode_solver::IVector_to_varlist(IVector & v, vector<variable*> & vars)
{
    for(int i = 0; i < v.size(); i++)
    {
        double lb = vars[i]->get_top_lb();
        double ub = vars[i]->get_top_ub();;
        if (lb < v[i].leftBound())
            vars[i]->set_top_lb(v[i].leftBound());
        if (ub > v[i].rightBound())
            vars[i]->set_top_ub(v[i].rightBound());
    }
}



void ode_solver::prune(vector<variable*>& _t_vars,
                       IVector v,
                       interval time,
                       vector<IVector> & out_v_list,
                       vector<interval> & out_time_list
    )
{
    bool candidate = true;
    for(int i = 0; candidate && i < v.size(); i++)
    {
        cerr << endl
             << "  v[" << i << "] = "
             << "[" << v[i].leftBound() << ", " << v[i].rightBound() << "]"
             << endl;
        cerr << "x_t[" << i << "] = "
             << "[" << _t_vars[i]->get_top_lb() << ", " << _t_vars[i]->get_top_ub() << "]"
             << endl;
        if (v[i].leftBound() > _t_vars[i]->get_top_ub() ||
            v[i].rightBound() < _t_vars[i]->get_top_lb())
        {
            candidate = false;
        }
    }
    cerr << "IS " << (candidate ? "CANDIDATE" : "NOT CANDIDATE") << endl;
    if (candidate) {
        out_v_list.push_back(v);
        out_time_list.push_back(time);
    }
}

bool ode_solver::solve()
{
    cerr << "ODE_Solver::solve" << endl;
    cout.precision(12);
    bool ret = true;
    try {
        // 1. Construct diff_sys, which are the ODE
        vector<variable*> _0_vars;
        vector<variable*> _t_vars;

        string diff_sys = create_diffsys_string(_ode_vars,
                                                _0_vars,
                                                _t_vars);

        //pass the problem with variables
        IMap vectorField(diff_sys);

        //initialize the solver
        ITaylor solver(vectorField,20,.1);
        ITimeMap timeMap(solver);

        //initial conditions
        IVector start = varlist_to_IVector(_0_vars);
        IVector end = varlist_to_IVector(_t_vars);

        //end = start; //set the initial comparison

        // define a doubleton representation of the interval vector start
        C0Rect2Set s(start);

        //time range
        variable* time = (*_0_vars.begin())->getODEtimevar();
        interval T = interval(time->get_top_lb(), time->get_top_ub());

        // double T = 100;

        timeMap.stopAfterStep(true);
        interval prevTime(0.);

        vector<IVector> out_v_list;
        vector<interval> out_time_list;
        do
        {
            timeMap(T,s);
            interval stepMade = solver.getStep();
            cout << "\nstep made: " << stepMade;

            const ITaylor::CurveType& curve = solver.getCurve();
            interval domain = interval(0,1)*stepMade;

            // a uniform grid
            int grid = 5;
            for(int i = 0; i <= grid; i++)
            {
                interval subsetOfDomain = interval(i,i+1)*stepMade/grid;
                intersection(domain,subsetOfDomain,subsetOfDomain);

                // v will contain rigorous bound for the trajectory for this time interval.
                IVector v = curve(subsetOfDomain);

                std::cout << "\nenclosure for t=" << prevTime + subsetOfDomain << ":  " << v;
                std::cout << "\ndiam(enclosure): " << diam(v);

                prune(_t_vars, v, subsetOfDomain, out_v_list, out_time_list);
            }
            prevTime = timeMap.getCurrentTime();
            cout << "\ncurrent time: " << prevTime << endl;

        } while (!timeMap.completed());

        // 1. Union all the out_v_list and intersect with end
        IVector vector_union = *(out_v_list.begin());
        for(vector<IVector>::iterator ite = out_v_list.begin();
            ite != out_v_list.end();
            ite++)
        {
            cerr << "U(" << vector_union << ", " << *ite << ") = ";
            vector_union = intervalHull (vector_union, *ite);
            cerr << vector_union << endl;
        }

        bool end_empty = false;
        // end = intersection \cap end;
        cerr << "Intersect(" << vector_union << ", " << end << ") = ";
        if(intersection(vector_union, end, end))
        {
            IVector_to_varlist(end, _t_vars);
            cerr << end << endl;
        }
        else {
            // intersection is empty!!
            end_empty = true;
            cerr << "empty" << endl;
            // for(int i = 0; end.size(); i++)
            // {
            //     end[i] = interval(+std::numeric_limits<double>::infinity(),
            //                       -std::numeric_limits<double>::infinity());
            // }
        }

        bool time_empty = false;
        // 2. Union all the out_time_list and intersect with T
        interval time_union = *out_time_list.begin();
        for(vector<interval>::iterator ite = out_time_list.begin();
            ite != out_time_list.end();
            ite++)
        {
            cerr << "U(" << time_union << ", " << *ite << ") = ";
            time_union = intervalHull(time_union, *ite);
            cerr << time_union << endl;
        }

        /* T = \cap (time_union, T) */
        // double lb = +std::numeric_limits<double>::infinity();
        // double ub = -std::numeric_limits<double>::infinity();

        cerr << "Intersect(" << time_union << ", " << T << ") = ";
        if(intersection(time_union, T, T))
        {
            time->set_top_lb(T.leftBound());
            time->set_top_ub(T.rightBound());
            cerr << T << endl;
        }
        else {
            /* there is no intersection, use empty interval [+oo, -oo] */
            time_empty = true;
            cerr << "empty" << endl;
        }

        // ...

        if(end_empty) {
            for(vector<variable*>::iterator ite = _t_vars.begin();
                ite != _t_vars.end();
                ite++)
            {
                (*ite)->set_empty_interval();
            }
            ret = false;
        } else {
            IVector_to_varlist(end, _t_vars);
        }

        if(time_empty) {
            time->set_empty_interval();
            ret = false;
        }

        //the following line detects conflicts in the trace
        // if(rp_box_empty(box)) {
        //     cout << "false here";
        //     return false;
        // }

        // rp_box_cout(box, 5, RP_INTERVAL_MODE_BOUND);
    }
    catch(std::exception& e)
    {
        cout << endl
             << endl
             << "Exception caught!" << endl
             << e.what() << endl << endl;
    }
    return ret;
}
