//solver for ODEs

#include "ode_solver.h"
#include "capd/capdlib.h"
#include <boost/algorithm/string/join.hpp>

using namespace capd;
using namespace std;

ode_solver::ode_solver(set < string > & odes,
                       set < variable* > & ode_vars
    ) :
    _odes(odes),
    _ode_vars(ode_vars)
{
}

ode_solver::~ode_solver()
{

}


bool ode_solver::solve(rp_box box)
{
    cout.precision(12);
    try {
        // 1. Construct diff_sys, which are the ODE
        //std::vector<Enode *>  diff_list;
        //std::vector<Enode *>  diff_var_list;
        std::map<int, int>    variables_to_intervals;
        std::vector<int> var_code; //stores the ids of variables in the formula

        vector<string> var_list;
        vector<string> ode_list;

        // 1. extract variables & functions
        for(set< string >::iterator ite = _odes.begin();
            ite != _odes.end();
            ite++)
        {
            size_t pos = ite->find("=");
            string var = ite->substr(0, pos - 1);
            string ode = ite->substr(pos + 1);
            cerr << "String : " << *ite << endl;
            cerr << "Var : " << var << endl;
            cerr << "Ode : " << ode << endl;

            var_list.push_back(var);
            var_list.push_back(ode);
        }

        // 2. join var_list to make diff_var, ode_list to diff_fun
        string diff_var = "var:" + boost::algorithm::join(var_list, ", ");
        string diff_fun = "fun:" + boost::algorithm::join(ode_list, ", ");

        cerr << "diff_var : " << diff_var << endl;
        cerr << "diff_fun : " << diff_fun << endl;

        string diff_sys = diff_var + diff_fun;

        //pass the problem with variables
        IMap vectorField(diff_sys);

        //initialize the solver
        ITaylor solver(vectorField,20,.1);
        ITimeMap timeMap(solver);

        //initial conditions
        IVector x(var_list.size());
        IVector y(var_list.size());

        y = x; //set the initial comparison

        int idx = 0, i=0;
        for (vector<string>::iterator var_ite = var_list.begin();
             var_ite != var_list.end();
             var_ite++)
        {
            double lb, ub;
            for(set<variable*>::iterator ode_var_ite = _ode_vars.begin();
                ode_var_ite != _ode_vars.end();
                ode_var_ite++)
            {
                if((*ode_var_ite)->get_enode()->getName().compare(*var_ite)) {
                    lb = (*ode_var_ite)->get_lb();
                    ub = (*ode_var_ite)->get_ub();
                    x[idx++] = interval(lb, ub);
                }
            }

            // //this is getting the initial intervals from the variables
            // //and give them to the initial conditions of odes in
            // //mkVar, a cons is added to the variable name
            // var_code.push_back(diff_var_list[i]->getCar()->getId());

            // x[i]=interval(rp_box_elem(box,variables_to_intervals[var_code[i]])[0].inf,
            //               rp_box_elem(box,variables_to_intervals[var_code[i]])[0].sup);

            // //note!! now the only problem is in this part. boxes are
            // //given to the wrong variables. wonder why. after fixing
            // //this, you are gonna give new bounds on variables based
            // //on the results from ode solving!
            cout<<"The interval on " << *var_ite << " is"<<x[i]<<endl;
        }

        // define a doubleton representation of the interval vector x
        C0Rect2Set s(x);

        //time range
        interval T=interval(0.0, 100.0);
        //double T = 100;

        timeMap.stopAfterStep(true);
        interval prevTime(0.);

        IVector v;
        IVector v_union(var_list.size());

        do
        {
            timeMap(T,s);
            interval stepMade = solver.getStep();
            cout << "\nstep made: " << stepMade;

            const ITaylor::CurveType& curve = solver.getCurve();
            interval domain = interval(0,1)*stepMade;

            // a uniform grid
            int grid = 5;
            for(int i = 0; i < grid; i++)
            {
                interval subsetOfDomain = interval(i,i+1)*stepMade/grid;
                intersection(domain,subsetOfDomain,subsetOfDomain);

                // v will contain rigorous bound for the trajectory for this time interval.
                v = curve(subsetOfDomain);

                std::cout << "\nenclosure for t=" << prevTime + subsetOfDomain << ":  " << v;

                //collect the intervals

                for(int j = 0; j < var_code.size(); j++)
                {
                    if (v_union[j].leftBound() == 0.0 && v_union[j].rightBound() == 0.0)
                    {
                        v_union = v;
                    }

                    if (v[j].leftBound()< v_union[j].leftBound())
                    {
                        v_union[j].setLeftBound(v[j].leftBound());
                    }

                    if (v[j].rightBound()> v_union[j].rightBound())
                    {
                        v_union[j].setRightBound(v[j].rightBound());
                    }

                }

                cout<<endl<<"current collection of points"<<v_union<<endl;
                //the following line controls whether you collect the set
                //	v_union = v;

            }
            prevTime = timeMap.getCurrentTime();
            cout << "\ncurrent time: " << prevTime << endl;

        }while(!timeMap.completed());

        //change this into time-sensitive
        //v_union = v;

        for(int j = 0; j < var_code.size(); j++)
        {
            if (v_union[j].leftBound()> rp_binf(rp_box_elem(box,variables_to_intervals[var_code[j]]+1)) )
            {
                //			cout<<"reassigned left"<<endl;
                rp_binf(rp_box_elem(box,variables_to_intervals[var_code[j]]+1)) = v_union[j].leftBound();
            }

            if (v_union[j].rightBound()< rp_bsup(rp_box_elem(box,variables_to_intervals[var_code[j]]+1)))
            {
                //			cout<<"reassigned right"<<endl;
                rp_bsup(rp_box_elem(box,variables_to_intervals[var_code[j]]+1)) = v_union[j].rightBound();
            }
        }

        //the following line detects conflicts in the trace
        if(rp_box_empty(box)) {
            cout << "false here";
            return false;
        }

        rp_box_cout(box, 5, RP_INTERVAL_MODE_BOUND);
        return true;
    }
    catch(std::exception& e)
    {
        cout << endl
             << endl
             << "Exception caught!" << endl
             << e.what() << endl << endl;
    }
}
