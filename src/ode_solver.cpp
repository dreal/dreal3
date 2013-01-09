//solver for ODEs

#include "ode_solver.h"
using namespace capd;

bool ode_solver::solve(rp_box box)
{
    cout.precision(12);
    try {
        // 1. Construct diff_sys, which are the ODE
        string diff_sys;           //, diff_var, diff_fun;
        std::vector<Enode *>  diff_list;
        std::vector<Enode *>  diff_var_list;
        std::map<int, int>    variables_to_intervals;
        std::vector<int> var_code; //stores the ids of variables in the formula

        // string tmp;

        // diff_var += "var:";
        // diff_fun += "fun:";

        // int i = 0;
        // set<int>::iterator ite;

        // for (ite = diff_group.begin(); ite!= diff_group.end(); ite++)
        // {
        //     int head_index;

        //     if (*ite>0)
        //     {
        //         head_index = diff_right_marker[*ite-1];
        //     }
        //     else
        //     {
        //         head_index = 0;
        //     }

        //     int tail_index = diff_right_marker[*ite];

        //     for (i= head_index; i<= tail_index; i++)
        //     {
        //         diff_var_list[i]->print_str(tmp);
        //         diff_var+= tmp;
        //         diff_var+= ",";
        //         tmp.clear();

        //         diff_list[i]->print_str(tmp);
        //         diff_fun+= tmp;
        //         diff_fun+= ",";
        //         tmp.clear();
        //     }
        // }

        // diff_var.erase(diff_var.end()-1);
        // diff_var += ";";
        // diff_fun.erase(diff_fun.end()-1);
        // diff_fun += ";";
        // diff_sys = diff_var + diff_fun;

        //pass the problem with variables
        IMap vectorField(diff_sys);

        //initialize the solver
        ITaylor solver(vectorField,20,.1);
        ITimeMap timeMap(solver);

        //initial conditions
        IVector x(diff_var_list.size());
        IVector y(diff_var_list.size());

        y = x; //set the initial comparison

        for (int i = 0; i < diff_var_list.size(); i++)
        {
            //this is getting the initial intervals from the variables
            //and give them to the initial conditions of odes in
            //mkVar, a cons is added to the variable name
            var_code.push_back(diff_var_list[i]->getCar()->getId());

            x[i]=interval(rp_box_elem(box,variables_to_intervals[var_code[i]])[0].inf,
                          rp_box_elem(box,variables_to_intervals[var_code[i]])[0].sup);

            //note!! now the only problem is in this part. boxes are
            //given to the wrong variables. wonder why. after fixing
            //this, you are gonna give new bounds on variables based
            //on the results from ode solving!
            cout<<"The interval on x"<<i<<" is"<<x[i]<<endl;
        }

        // define a doubleton representation of the interval vector x
        C0Rect2Set s(x);

        //time range
        interval T=interval(0.0, 100.0);
        //double T = 100;

        timeMap.stopAfterStep(true);
        interval prevTime(0.);

        IVector v;
        IVector v_union(diff_var_list.size());

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
