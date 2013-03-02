/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "ode_solver.h"
#include <boost/algorithm/string/join.hpp>
#include <limits>

using namespace capd;

ode_solver::ode_solver(set < Enode* > & ode_vars,
                       rp_box b,
                       std::map<Enode*, int>& enode_to_rp_id
    ) :
    _ode_vars(ode_vars),
    _b(b),
    _enode_to_rp_id(enode_to_rp_id)
{
}

ode_solver::~ode_solver()
{

}


string ode_solver::create_diffsys_string(set < Enode* > & ode_vars,
                                         vector<Enode*> & _0_vars,
                                         vector<Enode*> & _t_vars)
{
    vector<string> var_list;
    vector<string> ode_list;

    // 1. partition ode_vars into _0_vars and _t_vars by their ODE_vartype
    for(set< Enode* >::iterator ite = ode_vars.begin();
        ite != ode_vars.end();
        ite++)
    {
        cerr << (*ite)->getCar()->getName() << " = ["
             << get_lb(*ite)
             << ", "
             << get_ub(*ite)
             << "]" << endl;
        if ((*ite)->getODEvartype() == l_True) {
            _t_vars.push_back(*ite);
        }
        else if ((*ite)->getODEvartype() == l_False) {
            _0_vars.push_back(*ite);
            var_list.push_back((*ite)->getODEvarname());
            ode_list.push_back((*ite)->getODE());
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


IVector ode_solver::varlist_to_IVector(vector<Enode*> vars)
{
    IVector ret (vars.size());

    /* Assign current interval values */
    int i = 0;
    for (vector<Enode*>::iterator var_ite = vars.begin();
         var_ite != vars.end();
         var_ite++, i++)
    {
        double lb, ub;
        lb = get_lb(*var_ite);
        ub = get_ub(*var_ite);
        ret[i] = interval(lb, ub);
        cout << "The interval on "
             << (*var_ite)->getCar()->getName()
             << " is "<< ret[i] <<endl;
    }

    return ret;
}

void ode_solver::IVector_to_varlist(IVector & v, vector<Enode*> & vars)
{
    for(int i = 0; i < v.size(); i++)
    {
        double lb = get_lb(vars[i]);
        double ub = get_ub(vars[i]);
        if (lb < v[i].leftBound())
            set_lb(vars[i], v[i].leftBound());
        if (ub > v[i].rightBound())
            set_ub(vars[i], v[i].rightBound());
    }
}



void ode_solver::prune(vector<Enode*>& _t_vars,
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
             << "[" << get_lb(_t_vars[i]) << ", " << get_ub(_t_vars[i]) << "]"
             << endl;
        if (v[i].leftBound() > get_ub(_t_vars[i]) ||
            v[i].rightBound() < get_lb(_t_vars[i]))
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
        vector<Enode*> _0_vars;
        vector<Enode*> _t_vars;

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
        Enode* time = (*_0_vars.begin())->getODEtimevar();
        interval T = interval(get_lb(time), get_ub(time));
        cerr << "interval T = " << T << endl;
        // double T = 100;

        timeMap.stopAfterStep(true);
        interval prevTime(0.);

        vector<IVector> out_v_list;
        vector<interval> out_time_list;
        do
        {
            timeMap(T,s);
            interval stepMade = solver.getStep();
            cout << "step made: " << stepMade << endl;

            const ITaylor::CurveType& curve = solver.getCurve();
            interval domain = interval(0,1)*stepMade;

            // a uniform grid
            int grid = 5;
            interval subsetOfDomain = interval(0,1)*stepMade/grid;
            double incr = subsetOfDomain.rightBound();
            for(int i = 0; i < grid; i++)
            {
                intersection(domain,subsetOfDomain,subsetOfDomain);

                // v will contain rigorous bound for the trajectory for this time interval.
                IVector v = curve(subsetOfDomain);
                std::cout << "subset of domain =" << subsetOfDomain << endl;;
                std::cout << "enclosure for t=" << prevTime + subsetOfDomain << ":  " << v << endl;;
                std::cout << "diam(enclosure): " << diam(v) << endl;;

                prune(_t_vars, v, prevTime + subsetOfDomain, out_v_list, out_time_list);
                subsetOfDomain += interval(incr, incr);
            }
            prevTime = timeMap.getCurrentTime();
            cout << "current time: " << prevTime << endl;

        } while (!timeMap.completed());

        // 1. Union all the out_v_list and intersect with end
        IVector vector_union;
        bool end_empty = false;
        cerr << "Union and intersect V" << endl;
        if(out_v_list.size() == 0) {
            cerr << "There is nothing to collect for V" << endl;
            end_empty = true;
        } else {
            vector_union = *(out_v_list.begin());
            for(vector<IVector>::iterator ite = ++(out_v_list.begin());
                ite != out_v_list.end();
                ite++)
            {
                cerr << "U(" << vector_union << ", " << *ite << ") = ";
                vector_union = intervalHull (vector_union, *ite);
                cerr << vector_union << endl;
            }
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
        }

        cerr << endl << "Union and intersect time" << endl;
        bool time_empty = false;
        // 2. Union all the out_time_list and intersect with T
        interval time_union;

        if(out_time_list.size() == 0) {
            cerr << "There is nothing to collect for time" << endl;
            time_union = true;
        } else {
            time_union = *out_time_list.begin();
            for(vector<interval>::iterator ite = ++(out_time_list.begin());
                ite != out_time_list.end();
                ite++)
            {
                cerr << "U(" << time_union << ", " << *ite << ") = ";
                time_union = intervalHull(time_union, *ite);
                cerr << time_union << endl;
            }

            /* T = \cap (time_union, T) */

            cerr << "Intersect(" << time_union << ", " << T << ") = ";
            if(intersection(time_union, T, T))
            {
                set_lb(time, T.leftBound());
                set_ub(time, T.rightBound());
                cerr << T << endl;
            }
            else {
                /* there is no intersection, use empty interval [+oo, -oo] */
                time_empty = true;
                cerr << "empty" << endl;
            }
        }

        if(end_empty) {
            for(vector<Enode*>::iterator ite = _t_vars.begin();
                ite != _t_vars.end();
                ite++)
            {
                set_empty_interval(*ite);
            }
            ret = false;
        } else {
            IVector_to_varlist(end, _t_vars);
        }

        if(time_empty) {
            set_empty_interval(time);
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
