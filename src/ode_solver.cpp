//solver for ODEs

#include "ode_solver.h"
#include "capd/capdlib.h"
#include <boost/algorithm/string/join.hpp>

using namespace capd;
using namespace std;

ode_solver::ode_solver(set < variable* > & ode_vars) :
    _ode_vars(ode_vars)
{
}

ode_solver::~ode_solver()
{

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
        Enode* time = (*_0_vars.begin())->get_enode()->getODEtimevar();
        interval T = interval(time->getLowerBound(), time->getUpperBound());
        // double T = 100;

        timeMap.stopAfterStep(true);
        interval prevTime(0.);

        // IVector v;
        // IVector v_union(var_list.size());

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

                // //collect the intervals

                // for(int j = 0; j < var_code.size(); j++)
                // {
                //     if (v_union[j].leftBound() == 0.0 && v_union[j].rightBound() == 0.0)
                //     {
                //         v_union = v;
                //     }

                //     if (v[j].leftBound()< v_union[j].leftBound())
                //     {
                //         v_union[j].setLeftBound(v[j].leftBound());
                //     }

                //     if (v[j].rightBound()> v_union[j].rightBound())
                //     {
                //         v_union[j].setRightBound(v[j].rightBound());
                //     }

                // }

                // cout<<endl<<"current collection of points"<<v_union<<endl;
                //the following line controls whether you collect the set
                //	v_union = v;

            }
            prevTime = timeMap.getCurrentTime();
            cout << "\ncurrent time: " << prevTime << endl;

        } while (!timeMap.completed());

        // //change this into time-sensitive
        // //v_union = v;
        // int j = 0;
        // for(set<variable*>::iterator ite = _ode_vars.begin();
        //     ite != _ode_vars.end();
        //     ite++, j++)
        // {
        //     if (v_union[j].leftBound() > (*ite)->get_lb())
        //     {
        //         cout<<"reassigned left"<<endl;
        //         (*ite)->set_lb(v_union[j].leftBound());
        //     }

        //     if (v_union[j].rightBound() < (*ite)->get_ub())
        //     {
        //         cout << "reassigned right"<<endl;
        //         (*ite)->set_ub(v_union[j].rightBound());
        //     }
        // }

        // for(int j = 0; j < var_code.size(); j++)
        // {
        //     if (v_union[j].leftBound()> rp_binf(rp_box_elem(box,variables_to_intervals[var_code[j]]+1)) )
        //     {
        //         //			cout<<"reassigned left"<<endl;
        //         rp_binf(rp_box_elem(box,variables_to_intervals[var_code[j]]+1)) = v_union[j].leftBound();
        //     }

        //     if (v_union[j].rightBound()< rp_bsup(rp_box_elem(box,variables_to_intervals[var_code[j]]+1)))
        //     {
        //         //			cout<<"reassigned right"<<endl;
        //         rp_bsup(rp_box_elem(box,variables_to_intervals[var_code[j]]+1)) = v_union[j].rightBound();
        //     }
        // }

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
