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

#include <map>
#include <string>
#include <limits>
#include <math.h>
#include <boost/algorithm/string/join.hpp>
#include <boost/iterator/zip_iterator.hpp>
#include <boost/tuple/tuple.hpp>
#include "dsolvers/ode_solver.h"

using boost::algorithm::join;
using boost::make_zip_iterator;
using boost::tuple;
using capd::C0Rect2Set;
using capd::IFunction;
using capd::IMap;
using capd::ITaylor;
using capd::ITimeMap;
using capd::IVector;
using capd::interval;
using std::find_if;
using std::map;
using std::exception;

ode_solver::ode_solver(int group, SMTConfig& c, set<Enode*> const & ode_vars, rp_box b,
                       map<Enode*, int>& enode_to_rp_id) :
    _group(group),
    _config(c),
    _ode_vars(ode_vars),
    _b(b),
    _enode_to_rp_id(enode_to_rp_id),
    stepControl(c.nra_ODE_step) {

    // 1. partition ode_vars into _0_vars and _t_vars by their
    // ODE_vartype
    for_each(ode_vars.cbegin(),
             ode_vars.cend(),
             [this] (Enode* ode_var) {
                 // If this is _0 variable, then
                 if (ode_var->getODEvartype() == l_False) {
                     _0_vars.push_back(ode_var);
                     _t_vars.push_back(ode_var->getODEopposite());
                     var_list.push_back(ode_var->getODEvarname());
                     string const & ode = ode_var->getODE();
                     ode_list.push_back(ode);
                 }
             });
    // 2. join var_list to make diff_var, ode_list to diff_fun
    diff_var = "var:" + join(var_list, ", ") + ";";
    diff_fun = "fun:" + join(ode_list, ", ") + ";";

    // 3. construct diff_sys (string to CAPD)
    diff_sys = diff_var + diff_fun;
    if (_config.nra_verbose) {
        cerr << "diff_var : " << diff_var << endl;
        cerr << "diff_fun : " << diff_fun << endl;
        cerr << "diff_sys : " << diff_sys << endl;
    }
}

ode_solver::~ode_solver() {
}

void ode_solver::print_datapoint(ostream& out, interval const & t, interval const & v) const {
    out << "{ " << "\"time\": " << t << ", " << "\"enclosure\": " << v << "}";
}

void ode_solver::print_trace(ostream& out,
                             string const & key,
                             int const idx,
                             list<pair<interval, IVector>> const & trajectory) const {
    out << "{" << endl;
    out << "\t" << "\"key\": \"" << key << "\"," << endl;
    out << "\t" << "\"group\": \"" << _group << "\"," << endl;
    out << "\t" << "\"values\": [" << endl;
    auto iter = trajectory.cbegin();
    print_datapoint(out, iter->first, iter->second[idx]);
    for (++iter; iter != trajectory.cend(); iter++) {
        out << ", " << endl;
        print_datapoint(out, iter->first, iter->second[idx]);
    }
    out << endl;
    out << "\t" << "]" << endl;
    out << "}" << endl;
}

void ode_solver::print_trajectory(ostream& out) const {
    out.precision(12);
    out << "[" << endl;
    print_trace(out, var_list[0], 0, trajectory);
    for (size_t i = 1; i < var_list.size(); i++) {
        out << ", " << endl;
        print_trace(out, var_list[i], i, trajectory);
    }
    out << endl << "]" << endl;
}

void ode_solver::prune_trajectory(interval& time, IVector& e) {
    // Remove datapoints after time interval.
    auto ite = find_if (trajectory.begin(),
                        trajectory.end(),
                        [&time](pair<interval, IVector>& item) {
                            return item.first.leftBound() > time.rightBound();
                        });
    trajectory.erase(ite, trajectory.end());

    // Update the datapoints in the time interval
    ite = find_if (trajectory.begin(), trajectory.end(), [&time](pair<interval, IVector>& item) {
            return item.first.leftBound()>= time.leftBound();
        });
    for_each(ite, trajectory.end(), [&e](pair<interval, IVector>& item) {
            intersection(item.second, e, item.second);
        });
}

IVector ode_solver::varlist_to_IVector(vector<Enode*> const & vars) {
    IVector intvs (vars.size());
    /* Assign current interval values */
    for_each(make_zip_iterator(boost::make_tuple(vars.begin(), intvs.begin())),
             make_zip_iterator(boost::make_tuple(vars.end(), intvs.end())),
             [this] (tuple<Enode*, interval&> items) {
                 Enode* const & var = items.get<0>();
                 interval & intv = items.get<1>();
                 double lb = get_lb(var);
                 double ub = get_ub(var);
                 intv = interval(lb, ub);
                 if (_config.nra_verbose) { cerr << "The interval on " << var->getCar()->getName() << ": " << intv << endl; }
             });
    return intvs;
}

IVector ode_solver::extract_invariants(vector<Enode*> const & vars) {
    IVector ret (vars.size());
    int i = 0;
    for (auto var : vars) {
        pair<double, double> const & p = var->getODEinvariant();
        auto inv = interval(p.first, p.second);
        if (_config.nra_verbose) {
            cerr << "Invariant extracted from " << var->getCar()->getName() << " = " << inv << endl;
        }
        ret[i++] = inv;
    }
    return ret;
}

void ode_solver::IVector_to_varlist(IVector const & v, vector<Enode*> & vars) {
    for (auto i = 0; i < v.dimension(); i++) {
            double lb = get_lb(vars[i]);
            double ub = get_ub(vars[i]);
            if (lb < v[i].leftBound())
                set_lb(vars[i], v[i].leftBound());
            if (ub > v[i].rightBound())
                set_ub(vars[i], v[i].rightBound());
        }
}

// Save v and dt to out_v_list and out_time_list
// if they satisfy the following conditions:
// 1) dt should be inside of time
// 2) v should be inside of _t_vars
void ode_solver::prune(vector<Enode*> const & _t_vars, IVector const & v, interval const & dt, interval const & time,
                       vector<IVector> & out_v_list, vector<interval> & out_time_list) {
    if (_config.nra_verbose) { cerr << "  dt = " << dt   << endl << "time = " << time << endl; }
    if(!time.contains(dt)) {
        if (_config.nra_verbose) { cerr << "IS " << "NOT CANDIDATE (TIME)" << endl; }
        return;
    }
    for (auto i = 0; i < v.dimension(); i++) {
        if (_config.nra_verbose) {
            cerr << "  v[" << i << "] = " << v[i] << endl;
            cerr << "x_t[" << i << "] = " << _t_vars[i] << endl;
        }
        if ((v[i].leftBound() > get_ub(_t_vars[i])) || (v[i].rightBound() < get_lb(_t_vars[i]))) {
            if (_config.nra_verbose) { cerr << "IS " << "NOT CANDIDATE (" << i << ")" << endl; }
            return;
        }
    }
    if (_config.nra_verbose) { cerr << "IS " << "CANDIDATE" << endl; }
    out_v_list.push_back(v);
    out_time_list.push_back(dt);
}

bool ode_solver::simple_ODE() {
    vector<IFunction> funcs;
    for (auto ode_str : ode_list) {
        string const & func_str = diff_var + "fun:" + ode_str + ";";
        funcs.push_back(IFunction(func_str));
    };

    // initial conditions
    IVector X_0 = varlist_to_IVector(_0_vars);
    IVector inv = extract_invariants(_t_vars);
    IVector X_t = varlist_to_IVector(_t_vars);
    IVector new_X_t(X_t.dimension());

    // time range
    Enode* time = (*_0_vars.begin())->getODEtimevar();
    interval T = interval(get_lb(time), get_ub(time));

    bool ret = true;
    // X_t = X_t \cup (X_0 + (d/dt Inv) * T)
    for_each(make_zip_iterator(boost::make_tuple(X_0.begin(), X_t.begin(), funcs.begin())),
             make_zip_iterator(boost::make_tuple(X_0.end(), X_t.end(), funcs.end())),
             [&inv, &T, &ret, this] (tuple<interval&, interval&, IFunction&> item) {
                 if(ret) {
                     interval& x_0 = item.get<0>();
                     interval& x_t = item.get<1>();
                     IFunction& dxdt = item.get<2>();
                     try {
                         interval new_x_t = x_0 + dxdt(inv) * T;
                         if (!intersection(new_x_t, x_t, x_t)) {
                             if (_config.nra_verbose) {
                                 cerr << "Simple_ODE: no intersection for X_T" << endl;
                             }
                             ret = false;
                         }
                     } catch (exception& e) {
                         cerr << "Exception in Simple_ODE: " << e.what() << endl;
                     }
                 }
             });
    if (ret == false) {
        return ret;
    }
    // update
    IVector_to_varlist(X_t, _t_vars);

    // X_0 = X_0 \cup (X_t - + (d/dt Inv) * T)
    for_each(make_zip_iterator(boost::make_tuple(X_0.begin(), X_t.begin(), funcs.begin())),
             make_zip_iterator(boost::make_tuple(X_0.end(), X_t.end(), funcs.end())),
             [&inv, &T, &ret, this] (tuple<interval&, interval&, IFunction&> item) {
                 if (ret) {
                     interval& x_0 = item.get<0>();
                     interval& x_t = item.get<1>();
                     IFunction& dxdt = item.get<2>();
                     try {
                         interval new_x_0 = x_t - dxdt(inv) * T;
                         if (!intersection(new_x_0, x_0, x_0)) {
                             if (_config.nra_verbose) {
                                 cerr << "Simple_ODE: no intersection for X_0" << endl;
                             }
                             ret = false;
                         }
                     } catch (exception& e) {
                         cerr << "Exception in Simple_ODE: " << e.what() << endl;
                     }
                 }
             });
    if (ret == false) {
        return ret;
    }
    // update
    IVector_to_varlist(X_0, _0_vars);
    return true;
}

bool ode_solver::solve_forward() {
    if (_config.nra_verbose) {
        cerr << "ODE_Solver::solve_forward()" << endl;
    }
    cerr.precision(12);
    try {
        // pass the problem with variables
        IMap vectorField(diff_sys);
        // initialize the solver
        // The solver uses high order enclosure method to verify the existence of the solution.
        // The order will be set to 20.
        // The time step (when step control is turned off) will be 0.1.
        // The time step control is turned on by default but the solver must know if we want to
        // integrate forwards or backwards (then put negative number).
        ITaylor solver(vectorField, _config.nra_ODE_taylor_order, .1); /* HERE */
        ITimeMap timeMap(solver);
        // initial conditions
        IVector start = varlist_to_IVector(_0_vars);
        IVector inv = extract_invariants(_t_vars);
        IVector end = varlist_to_IVector(_t_vars);
        // define a doubleton representation of the interval vector start
        C0Rect2Set s(start);
        // time range
        Enode* time = (*_0_vars.begin())->getODEtimevar();
        interval T = interval(get_lb(time), get_ub(time));
        if (_config.nra_verbose) {
            cerr << "interval T = " << T << endl;
        }
        timeMap.stopAfterStep(true);
        bool fastForward = true;
        if (stepControl == 0.0) {
            timeMap.turnOnStepControl();
        } else {
            timeMap.turnOffStepControl();
            timeMap.setStep(stepControl);
        }
        interval prevTime(0.);
        if (_config.nra_json) {
            trajectory.clear();
            trajectory.push_back(make_pair(timeMap.getCurrentTime(), IVector(s)));
        }
        vector<IVector> out_v_list;
        vector<interval> out_time_list;
        bool invariantViolated = false;
        do {
            invariantViolated = !check_invariant(s, inv);
            timeMap(T.rightBound(), s);
            if(contain_NaN(s)) { return true; }
            interval stepMade = solver.getStep();
            // cerr << "step made: " << stepMade << endl;
            if (_config.nra_verbose) {
                cerr << "step made: " << stepMade << endl
                     << "T : " << T << endl
                     << "currentTime : " << timeMap.getCurrentTime() << endl;
            }
            if (!fastForward || T.leftBound() <= timeMap.getCurrentTime().rightBound()) {
                // This is how we can extract an information about the
                // trajectory between time steps. The type CurveType
                // is a function defined on the interval [0,stepMade].
                // It can be evaluated at a point (or interval). The
                // curve can be also differentiated wrt to time. We
                // can also extract from it the 1-st order derivatives
                // wrt.
                const ITaylor::CurveType& curve = solver.getCurve();
                interval domain = interval(0, 1) * stepMade;
                double domainWidth = domain.rightBound() - domain.leftBound();
                // Here we use a uniform grid of last time step made
                // to enclose the trajectory between time steps.
                // You can use your own favourite subdivision, perhaps nonuniform,
                // depending on the problem you want to solve.
                for (unsigned i = 0; i <_config.nra_ODE_grid_size; i++) {
                    interval subsetOfDomain = domain / _config.nra_ODE_grid_size
                        + (domainWidth / _config.nra_ODE_grid_size) * i;
                    // The above interval does not need to be a subset of domain.
                    // This is due to rounding to floating point numbers.
                    // We take the intersection with the domain.
                    intersection(domain, subsetOfDomain, subsetOfDomain);
                    // Here we evaluated curve at the interval subsetOfDomain.
                    // v will contain rigorous bound for the trajectory for this time interval.
                    IVector v = curve(subsetOfDomain);
                    if (_config.nra_verbose) {
                        cerr << "subsetOfDomain: " << subsetOfDomain << endl
                             << "enclosure for t=" << prevTime + subsetOfDomain << ": " << v << endl
                             << "diam(enclosure): " << diam(v) << endl;
                    }
                    if (!check_invariant(v, inv)) {
                        invariantViolated = true;
                        break;
                    }
                    if (_config.nra_verbose) {
                        cerr << "inv = " << inv << endl;
                        cerr << "v = " << v << endl;
                        cerr << "enclosure for t intersected with inv " << prevTime + subsetOfDomain << ": " << v << endl;
                    }
                    if (_config.nra_json) {
                        trajectory.push_back(make_pair(prevTime + subsetOfDomain, v));
                    }
                    prune(_t_vars, v, prevTime + subsetOfDomain, T, out_v_list, out_time_list);
                }
            } else {
                if (_config.nra_verbose) {
                    cerr << "Fast-forward:: " << prevTime << " ===> " << timeMap.getCurrentTime() << endl;
                    cerr << "enclosure for t=" << timeMap.getCurrentTime() << ": " << IVector(s) << endl;
                }
                if (_config.nra_json) {
                    trajectory.push_back(make_pair(timeMap.getCurrentTime(), IVector(s)));
                }
            }
            prevTime = timeMap.getCurrentTime();
            if (_config.nra_verbose) {
                cerr << "current time: " << prevTime << endl;
            }
            if (_config.nra_verbose) {
                cerr << "InvViolated : " << invariantViolated << endl
                     << "timeMap.completed: " << timeMap.completed() <<  endl;
            }
        } while (!invariantViolated && !timeMap.completed());
        if (union_and_join(out_v_list, end)) {
            _t_vars.clear();
            return false;
        } else {
            IVector_to_varlist(end, _t_vars);
        }
        if (union_and_join(out_time_list, T)) {
            set_empty_interval(time);
            return false;
        } else {
            set_lb(time, T.leftBound());
            set_ub(time, T.rightBound());
        }
        if (_config.nra_json) {
            prune_trajectory(T, end);
        }
    } catch(exception& e) {
        // if (_config.nra_verbose) {
        cerr << "Exception in ODE Solving (Forward)" << endl
             << e.what() << endl;
        // }
    }
    return true;
}

bool ode_solver::solve_backward() {
    return true;
}

/**
    \brief return false if IVector \c v violates a given invariant \c inv.
*/
bool ode_solver::check_invariant(IVector & v, IVector const & inv) {
    if (!intersection(v, inv, v)) {
        if (_config.nra_verbose) {
            cerr << "invariant violated!" << endl;
            for (auto i = 0; i < v.dimension(); i++) {
                if (v[i].leftBound() < inv[i].leftBound() || v[i].rightBound() > inv[i].rightBound()) {
                    cerr << "inv[" << i << "] = " << inv[i] << endl;
                    cerr << "  v[" << i << "] = " <<   v[i] << endl;
                }
            }
        }
        return false;
    }
    return true;
}

bool ode_solver::check_invariant(C0Rect2Set & s, IVector const & inv) {
    static thread_local IVector v;
    v = IVector(s);
    bool r = check_invariant(v, inv);
    s = C0Rect2Set(v);
    return r;
}

bool ode_solver::contain_NaN(IVector const & v) {
    for (interval const & i : v) {
        if (std::isnan(i.leftBound()) || std::isnan(i.rightBound())) {
            if (_config.nra_verbose) { cerr << "NaN Found! : " << v << endl; }
            return true;
        }
    }
    return false;
}

bool ode_solver::contain_NaN(C0Rect2Set const & s) {
    return contain_NaN(IVector(s));
}


/**
    \brief Take union of all values in \c bucket, intersection with
    \c result, and return result.

    If the result is empty, it return true, otherwise return false
*/
template<typename T>
bool ode_solver::union_and_join(vector<T> const & bucket, T & result) {
    // 1. u = Union of all the elements of bucket
    if (bucket.size() == 0) {
        if (_config.nra_verbose) {
            cerr << "Union_Join: collect from the bucket" << endl;
        }
        return true;
    }
    static thread_local T u;
    u = *(bucket.cbegin());
    for (auto ite = ++(bucket.cbegin()); ite != bucket.cend(); ite++) {
        if (_config.nra_verbose) {
            cerr << "U(" << u << ", " << *ite << ") = ";
        }
        u = intervalHull(u, *ite);
        if (_config.nra_verbose) {
            cerr << u << endl;
        }
    }
    // 2. result = intersection(u, result);
    if (_config.nra_verbose) {
        cerr << "Intersect(" << u << ", " << result << ") = ";
    }
    if (intersection(u, result, result)) {
        if (_config.nra_verbose) {
            cerr << result << endl;
        }
    } else {
        // intersection is empty!!
        if (_config.nra_verbose) {
            cerr << "empty" << endl;
        }
        return true;
    }
    return false;
}
