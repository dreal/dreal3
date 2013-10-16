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
             [&] (Enode* ode_var) {
                 // If this is _0 variable, then
                 if (ode_var->getODEvartype() == l_False) {
                     _0_vars.push_back(ode_var);
                     _t_vars.push_back(ode_var->getODEopposite());
                     var_list.push_back(ode_var->getODEvarname());
                     string const & ode = ode_var->getODE();
                     ode_list.push_back(ode);
                 }
             });
    // 2. join var_list to make diff_var, ode_list to diff_fun_forward
    diff_var = "var:" + join(var_list, ", ") + ";";
    diff_fun_forward = "fun:" + join(ode_list, ", ") + ";";
    diff_fun_backward = "fun: -" + join(ode_list, ", -") + ";";

    // 3. construct diff_sys_forward (string to CAPD)
    diff_sys_forward = diff_var + diff_fun_forward;
    diff_sys_backward = diff_var + diff_fun_backward;
    if (_config.nra_verbose) {
        cerr << "diff_var : " << diff_var << endl;
        cerr << "diff_fun_forward : " << diff_fun_forward << endl;
        cerr << "diff_sys_forward : " << diff_sys_forward << endl;
        cerr << "diff_fun_backward : " << diff_fun_backward << endl;
        cerr << "diff_sys_backward : " << diff_sys_backward << endl;
    }
    // 4. setup X_0, X_t, inv, T
    X_0 = varlist_to_IVector(_0_vars);
    inv = extract_invariants(_t_vars);
    X_t = varlist_to_IVector(_t_vars);
    time = (*_0_vars.begin())->getODEtimevar();
    T = interval(get_lb(time), get_ub(time));
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
             [&] (tuple<Enode*, interval&> items) {
                 Enode* const & var = items.get<0>();
                 interval & intv = items.get<1>();
                 double lb = get_lb(var);
                 double ub = get_ub(var);
                 intv = interval(lb, ub);
                 if (_config.nra_verbose) {
                     cerr << "The interval on "
                          << var->getCar()->getName()
                          << ": " << intv << endl;
                 }
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

// Save v and dt to v_bucket and time_bucket
// if they satisfy the following conditions:
// 1) dt should be inside of time
// 2) v should be inside of _t_vars
void ode_solver::prune(vector<Enode*> const & _t_vars, IVector const & v, interval const & dt, interval const & time,
                       vector<IVector> & v_bucket, vector<interval> & time_bucket) {
    if (_config.nra_verbose) {
        cerr << "  dt = " << dt   << endl;
        cerr << "time = " << time << endl;
    }
    if(dt.leftBound() > time.rightBound() || time.leftBound() > dt.rightBound()) {
        if (_config.nra_verbose) {
            cerr << "IS " << "NOT CANDIDATE (TIME)" << endl;
        }
        return;
    }
    for (auto i = 0; i < v.dimension(); i++) {
        if (_config.nra_verbose) {
            cerr << "  v[" << i << "] = " << v[i] << endl;
            cerr << "x_t[" << i << "] = " << _t_vars[i] << endl;
        }
        if ((v[i].leftBound() > get_ub(_t_vars[i])) || (v[i].rightBound() < get_lb(_t_vars[i]))) {
            if (_config.nra_verbose) {
                cerr << "IS " << "NOT CANDIDATE (" << i << ")" << endl;
            }
            return;
        }
    }
    if (_config.nra_verbose) {
        cerr << "IS " << "CANDIDATE" << endl;
    }
    v_bucket.push_back(v);
    time_bucket.push_back(dt);
}

bool ode_solver::simple_ODE() {
    cerr << "SIMPLE" << endl;
    vector<IFunction> funcs;
    for (auto ode_str : ode_list) {
        string const & func_str = diff_var + "fun:" + ode_str + ";";
        funcs.push_back(IFunction(func_str));
    };
    return simple_ODE_forward(X_0, X_t, T, inv, funcs) && simple_ODE_backward(X_0, X_t, T, inv, funcs);
}

bool ode_solver::solve_forward() {
    cerr << "FORWARD" << endl;
    if (_config.nra_verbose) {
        cerr << "ODE_Solver::solve_forward()" << endl;
    }
    bool ret = true;
    try {
        IMap vectorField(diff_sys_forward);
        ITaylor solver(vectorField, _config.nra_ODE_taylor_order, .1);
        ITimeMap timeMap(solver);
        C0Rect2Set s(X_0);
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
        vector<IVector> v_bucket;
        vector<interval> time_bucket;
        bool invariantViolated = false;
        do {
            cerr << "F" << timeMap.getCurrentTime() << " ";
            invariantViolated = !check_invariant(s, inv);
            timeMap(T.rightBound(), s);
            if(contain_NaN(s)) { return true; }
            if (_config.nra_verbose) {
                cerr << "T : " << T << endl
                     << "currentTime : " << timeMap.getCurrentTime() << endl;
                // << "step made: " << stepMade << endl
            }
            if (!fastForward || T.leftBound() <= timeMap.getCurrentTime().rightBound()) {
                invariantViolated = inner_loop_forward(solver, prevTime, v_bucket, time_bucket);
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
        cerr << endl;
        if (union_and_join(v_bucket, X_t)) {
            IVector_to_varlist(X_t, _t_vars);
        } else {
            for (auto _t_var : _t_vars) {
                set_empty_interval(_t_var);
            }
            ret = false;
        }
        if (union_and_join(time_bucket, T)) {
            set_lb(time, T.leftBound());
            set_ub(time, T.rightBound());
        } else {
            set_empty_interval(time);
            ret = false;
        }
        if (_config.nra_json) {
            prune_trajectory(T, X_t);
        }
    } catch(exception& e) {
        if (_config.nra_verbose) {
            cerr << "Exception in ODE Solving (Forward)" << endl
                 << e.what() << endl;
        }
        cerr << "FORWARD - EXCEPTION" << endl;
        return true;
    }
    cerr << "FORWARD" << endl;
    return ret;
}

bool ode_solver::solve_backward() {
    cerr << "BACKWARD" << endl;
    if (_config.nra_verbose) {
        cerr << "ODE_Solver::solve_forward()" << endl;
    }
    bool ret = true;
    try {
        IMap vectorField(diff_sys_backward);
        ITaylor solver(vectorField, _config.nra_ODE_taylor_order, .1);
        ITimeMap timeMap(solver);
        C0Rect2Set s(X_t);
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
        // if (_config.nra_json) {
        //     trajectory.clear();
        //     trajectory.push_back(make_pair(timeMap.getCurrentTime(), IVector(s)));
        // }
        vector<IVector> v_bucket;
        vector<interval> time_bucket;
        bool invariantViolated = false;
        do {
            cerr << "B" << timeMap.getCurrentTime() << " ";
            invariantViolated = !check_invariant(s, inv);
            timeMap(T.rightBound(), s);
            if(contain_NaN(s)) { return true; }
            if (_config.nra_verbose) {
                cerr << "T : " << T << endl
                     << "currentTime : " << timeMap.getCurrentTime() << endl;
                // << "step made: " << stepMade << endl
            }
            if (!fastForward || T.leftBound() <= timeMap.getCurrentTime().rightBound()) {
                invariantViolated = inner_loop_backward(solver, prevTime, v_bucket, time_bucket);
            } else {
                if (_config.nra_verbose) {
                    cerr << "Fast-forward:: " << prevTime << " ===> " << timeMap.getCurrentTime() << endl;
                    cerr << "enclosure for t=" << timeMap.getCurrentTime() << ": " << IVector(s) << endl;
                }
                // if (_config.nra_json) {
                //     trajectory.push_back(make_pair(timeMap.getCurrentTime(), IVector(s)));
                // }

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
        cerr << endl;
        if (union_and_join(v_bucket, X_0)) {
            IVector_to_varlist(X_0, _0_vars);
        } else {
            for (auto _0_var : _0_vars) {
                set_empty_interval(_0_var);
            }
            ret = false;
        }
        if (union_and_join(time_bucket, T)) {
            set_lb(time, T.leftBound());
            set_ub(time, T.rightBound());
        } else {
            set_empty_interval(time);
            ret = false;
        }
        // if (_config.nra_json) {
        //     prune_trajectory(T, X_0);
        // }
    } catch(exception& e) {
        if (_config.nra_verbose) {
            cerr << "Exception in ODE Solving (Backward)" << endl
                 << e.what() << endl;
         }
        cerr << "BACKWARD - EXCEPTION" << endl;
        return true;
    }
    cerr << "BACKWARD" << endl;
    return ret;
}

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
    IVector v(s);
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

template<typename V>
bool ode_solver::union_and_join(vector<V> const & bucket, V & result) {
    // 1. u = Union of all the elements of bucket
    if (bucket.size() == 0) {
        if (_config.nra_verbose) {
            cerr << "Union_Join: collect from the bucket" << endl;
        }
        return false;
    }
    V u = *(bucket.cbegin());
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
        return false;
    }
    return true;
}

// Run inner loop
// return true if it violates invariant otherwise return false.
bool ode_solver::inner_loop_forward(ITaylor & solver, interval const & prevTime,
                                    vector<IVector> & v_bucket, vector<interval> & time_bucket) {
    interval stepMade = solver.getStep();
    const ITaylor::CurveType& curve = solver.getCurve();
    interval domain = interval(0, 1) * stepMade;
    double domainWidth = domain.rightBound() - domain.leftBound();
    for (unsigned i = 0; i <_config.nra_ODE_grid_size; i++) {
        interval subsetOfDomain = domain / _config.nra_ODE_grid_size
            + (domainWidth / _config.nra_ODE_grid_size) * i;
        intersection(domain, subsetOfDomain, subsetOfDomain);
        IVector v = curve(subsetOfDomain);
        if (_config.nra_verbose) {
            cerr << "subsetOfDomain: " << subsetOfDomain << endl
                 << "enclosure for t=" << prevTime + subsetOfDomain << ": " << v << endl
                 << "diam(enclosure): " << diam(v) << endl;
        }
        if (!check_invariant(v, inv)) {
            return true;
        }
        if (_config.nra_verbose) {
            cerr << "inv = " << inv << endl;
            cerr << "v = " << v << endl;
            cerr << "enclosure for t intersected with inv " << prevTime + subsetOfDomain << ": " << v << endl;
        }
        if (_config.nra_json) {
            trajectory.push_back(make_pair(prevTime + subsetOfDomain, v));
        }
        prune(_t_vars, v, prevTime + subsetOfDomain, T, v_bucket, time_bucket);
    }
    return false;
}

// Run inner loop
// return true if it violates invariant otherwise return false.
bool ode_solver::inner_loop_backward(ITaylor & solver, interval const & prevTime,
                                    vector<IVector> & v_bucket, vector<interval> & time_bucket) {
    interval stepMade = solver.getStep();
    const ITaylor::CurveType& curve = solver.getCurve();
    interval domain = interval(0, 1) * stepMade;
    double domainWidth = domain.rightBound() - domain.leftBound();
    for (unsigned i = 0; i <_config.nra_ODE_grid_size; i++) {
        interval subsetOfDomain = domain / _config.nra_ODE_grid_size
            + (domainWidth / _config.nra_ODE_grid_size) * i;
        intersection(domain, subsetOfDomain, subsetOfDomain);
        IVector v = curve(subsetOfDomain);
        if (_config.nra_verbose) {
            cerr << "subsetOfDomain: " << subsetOfDomain << endl
                 << "enclosure for t=" << prevTime + subsetOfDomain << ": " << v << endl
                 << "diam(enclosure): " << diam(v) << endl;
        }
        if (!check_invariant(v, inv)) {
            return true;
        }
        if (_config.nra_verbose) {
            cerr << "inv = " << inv << endl;
            cerr << "v = " << v << endl;
            cerr << "enclosure for t intersected with inv " << prevTime + subsetOfDomain << ": " << v << endl;
        }
        // if (_config.nra_json) {
        //     trajectory.push_back(make_pair(prevTime + subsetOfDomain, v));
        // }
        prune(_0_vars, v, prevTime + subsetOfDomain, T, v_bucket, time_bucket);
    }
    return false;
}


bool ode_solver::simple_ODE_forward(IVector const & X_0, IVector & X_t, interval const & T,
                                    IVector const & inv, vector<IFunction> const & funcs) {
    // X_t = X_t \cup (X_0 + (d/dt Inv) * T)
    for(int i = 0; i < X_0.dimension(); i++) {
        interval const & x_0 = X_0[i];
        interval & x_t = X_t[i];
        IFunction const & dxdt = funcs[i];
        try {
            interval new_x_t = x_0 + dxdt(inv) * T;
            if (!intersection(new_x_t, x_t, x_t)) {
                if (_config.nra_verbose) {
                    cerr << "Simple_ODE: no intersection for X_T" << endl;
                }
                return false;
            }
        } catch (exception& e) {
            cerr << "Exception in Simple_ODE: " << e.what() << endl;
        }
    }
    // update
    IVector_to_varlist(X_t, _t_vars);
    return true;
}

bool ode_solver::simple_ODE_backward(IVector & X_0, IVector const & X_t, interval const & T,
                                     IVector const & inv, vector<IFunction> const & funcs) {
    // X_0 = X_0 \cup (X_t - + (d/dt Inv) * T)
    for(int i = 0; i < X_0.dimension(); i++) {
        interval & x_0 = X_0[i];
        interval const & x_t = X_t[i];
        IFunction const & dxdt = funcs[i];
        try {
            interval const new_x_0 = x_t - dxdt(inv) * T;
            if (!intersection(new_x_0, x_0, x_0)) {
                if (_config.nra_verbose) {
                    cerr << "Simple_ODE: no intersection for X_0" << endl;
                }
                return false;
            }
        } catch (exception& e) {
            cerr << "Exception in Simple_ODE: " << e.what() << endl;
        }
    }
    // update
    IVector_to_varlist(X_0, _0_vars);
    return true;
}
