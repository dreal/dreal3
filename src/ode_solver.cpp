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
        if (v[i].leftBound() > _t_vars[i]->get_ub() ||
            v[i].rightBound() > _t_vars[i]->get_lb())
        {
            candidate = false;
        }
    }

    if (candidate) {
        out_v_list.push_back(v);
        out_time_list.push_back(time);
    }
}

bool ode_solver::solve()
{
    cerr << "==============================" << endl;
    cerr << "ODE_Solver::solve" << endl;
    for(set<variable*>::iterator ite = _ode_vars.begin();
        ite != _ode_vars.end();
        ite++)
    {
        cerr << "ODE Vars" << "\t";
        cerr << "Name: " << (*ite)->getName() << "\t";
        cerr << "[" << (*ite)->get_lb() << ", ";
        cerr << (*ite)->get_ub() << "]" << endl;
    }

    cout.precision(12);
    try {
        // 1. Construct diff_sys, which are the ODE
        //std::vector<Enode *>  diff_list;
        //std::vector<Enode *>  diff_var_list;
        std::map<int, int>    variables_to_intervals;
        std::vector<int> var_code; //stores the ids of variables in the formula

        vector<string> var_list;
        vector<string> ode_list;


        vector<variable*> _0_vars;
        vector<variable*> _t_vars;

        // 1. partition _ode_vars into _0_vars and _t_vars by their ODE_vartype
        for(set< variable* >::iterator ite = _ode_vars.begin();
            ite != _ode_vars.end();
            ite++)
        {
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

        //pass the problem with variables
        IMap vectorField(diff_sys);

        //initialize the solver
        ITaylor solver(vectorField,20,.1);
        ITimeMap timeMap(solver);

        //initial conditions
        IVector start(_0_vars.size());
        IVector end(_t_vars.size());

        end = start; //set the initial comparison

        /* Assign current interval values as X0 */
        int idx = 0;
        for (vector<variable*>::iterator var_ite = _0_vars.begin();
             var_ite != _0_vars.end();
             var_ite++, idx++)
        {
            double lb, ub;
            lb = (*var_ite)->get_lb();
            ub = (*var_ite)->get_ub();
            start[idx] = interval(lb, ub);
            cout << "The interval on "
                 << (*var_ite)->getName()
                 << " is "<< start[idx] <<endl;
        }

        // define a doubleton representation of the interval vector start
        C0Rect2Set s(start);

        //time range
        /* TODO: This should be of type variable, not Enode* */
        Enode* time = (*_0_vars.begin())->get_enode()->getODEtimevar();
        interval T = interval(time->getLowerBound(), time->getUpperBound());
        // double T = 100;

        timeMap.stopAfterStep(true);
        interval prevTime(0.);

        // IVector v;
        // IVector v_union(var_list.size());

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

        // 1. Union all the out_v_list & out_time_list
        // 1-1. Union over out_v_list
        IVector union_result(_t_vars.size());
        for(int i = 0; i < union_result.size(); i++)
        {
            union_result[i] = interval(+std::numeric_limits<double>::infinity(),
                                       -std::numeric_limits<double>::infinity());
        }
        for(vector<IVector>::iterator ite = out_v_list.begin();
            ite != out_v_list.end();
            ite++)
        {
            for(int i = 0; i < union_result.size(); i++)
            {
                double tmp_lb = (*ite)[i].leftBound();
                double tmp_ub = (*ite)[i].rightBound();

                if (tmp_lb >= union_result[i].leftBound())
                    tmp_lb = union_result[i].leftBound();

                if (tmp_ub <= union_result[i].rightBound())
                    tmp_ub = union_result[i].rightBound();

                union_result[i] = interval(tmp_lb, tmp_ub);
            }
        }

        // 1-2. intersection with out_v_list and X_t
        for(int i = 0; i < union_result.size(); i++)
        {
            double x_t_i_lb = _t_vars[i]->get_lb();
            double x_t_i_ub = _t_vars[i]->get_ub();;

            if (x_t_i_lb < union_result[i].leftBound())
                _t_vars[i]->set_lb(union_result[i].leftBound());

            if (x_t_i_ub > union_result[i].rightBound())
                _t_vars[i]->set_ub(union_result[i].rightBound());
        }

        // 2-1. Union over out_time_list
        double lb = +std::numeric_limits<double>::infinity();
        double ub = -std::numeric_limits<double>::infinity();
        for(vector<interval>::iterator ite = out_time_list.begin();
            ite != out_time_list.end();
            ite++)
        {
            double tmp_lb = (*ite).leftBound();
            double tmp_ub = (*ite).rightBound();

            if (tmp_lb < lb)
                lb = tmp_lb;

            if (tmp_ub > ub)
                ub = tmp_ub;
        }

        // 2-2. intersection with out_time_list and time
        if (lb > T.leftBound())
            time->setLowerBound(lb);
        if (ub < T.rightBound())
            time->setUpperBound(ub);

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
    return true;

}
