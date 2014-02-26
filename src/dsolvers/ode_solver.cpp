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

#include <time.h>
#include <limits>
#include <math.h>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <sstream>
#include "dsolvers/ode_solver.h"
#include "dsolvers/util/logger.h"
#include "dsolvers/util/string.h"
using capd::C0Rect2Set;
using capd::IFunction;
using capd::IMap;
using capd::ITaylor;
using capd::ITimeMap;
using capd::IVector;
using capd::interval;
using std::exception;
using std::find_if;
using std::max;
using std::numeric_limits;
using std::reverse;
using std::stoi;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unordered_map;
using std::unordered_set;

ode_solver::ode_solver(SMTConfig& c,
                       Egraph & e,
                       Enode * l_int,
                       vector<Enode*> invs,
                       unordered_map<Enode*, int>& enode_to_rp_id) :
    m_config(c),
    m_egraph(e),
    m_int(l_int),
    m_invs(invs),
    m_enode_to_rp_id(enode_to_rp_id),
    m_stepControl(c.nra_ODE_step),
    m_time(nullptr) {
    m_mode = l_int->getCdr()->getCar()->getValue();
    map<string, Enode *> & flow_map = m_egraph.flow_maps[string("flow_") + to_string(m_mode)];
    m_time = l_int->getCdr()->getCdr()->getCdr()->getCar();
    string time_str = m_time->getCar()->getName();
    m_step = stoi(time_str.substr(time_str.find_last_of("_") + 1));
    Enode * p = l_int->getCdr()->getCdr()->getCdr()->getCdr();
    while (!p->isEnil()) {
        string name = p->getCar()->getCar()->getName();
        size_t second_ = name.find_last_of("_");
        size_t first_ = name.find_last_of("_", second_ - 1);
        string name_prefix, name_postfix;
        if (first_ == string::npos) {
            name_prefix = name.substr(0, second_);
            name_postfix = name.substr(second_);
        } else {
            name_prefix = name.substr(0, first_);
            name_postfix = name.substr(first_);
        }
        if (flow_map.find(name_prefix) == flow_map.end()) {
            cerr << name_prefix << " is not found in flow_map." << endl;
            assert(flow_map.find(name_prefix) != flow_map.end());
        }
        Enode * rhs = flow_map[name_prefix];
        stringstream ss;
        rhs->print_infix(ss, true, name_postfix);
        if (rhs->isConstant() && rhs->getValue() == 0.0) {
            m_pars.push_back(p->getCar());
            m_par_list.push_back(name);
        } else {
            m_0_vars.push_back(p->getCar());
            m_t_vars.push_back(p->getCdr()->getCar());
            m_var_list.push_back(name);
            m_ode_list.push_back(ss.str());
        }
        p = p->getCdr()->getCdr();
    }

    // join var_list to make diff_var, ode_list to diff_fun_forward
    string diff_var = "var:" + join(m_var_list, ", ") + ";";
    string diff_fun_forward = "fun:" + join(m_ode_list, ", ") + ";";
    string diff_fun_backward = "fun: -" + join(m_ode_list, ", -") + ";";

    // construct diff_sys_forward (string to CAPD)
    string diff_par;
    if (m_par_list.size() > 0) {
        diff_par = "par:" + join(m_par_list, ", ") + ";";
        m_diff_sys_forward = diff_par;
        m_diff_sys_backward = diff_par;
    }
    m_diff_sys_forward  += diff_var + diff_fun_forward;
    m_diff_sys_backward += diff_var + diff_fun_backward;
    DREAL_LOG_DEBUG("diff_par          : " << diff_par);
    DREAL_LOG_DEBUG("diff_var          : " << diff_var);
    DREAL_LOG_DEBUG("diff_fun_forward  : " << diff_fun_forward);
    DREAL_LOG_DEBUG("diff_fun_backward : " << diff_fun_backward);
    DREAL_LOG_DEBUG("diff_sys_forward  : " << m_diff_sys_forward);
    DREAL_LOG_DEBUG("diff_sys_backward : " << m_diff_sys_backward);

    for (auto ode_str : m_ode_list) {
        string const func_str = diff_par + diff_var + "fun:" + ode_str + ";";
        m_funcs.push_back(IFunction(func_str));
    };
    m_inv = extract_invariants();
}

ode_solver::~ode_solver() {
}

void ode_solver::update(rp_box b) {
    m_b = b;
    m_X_0 = varlist_to_IVector(m_0_vars);
    m_X_t = varlist_to_IVector(m_t_vars);
    m_T = interval(get_lb(m_time), get_ub(m_time));
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
    out << "\t" << "\"mode\": \"" << m_mode << "\"," << endl;
    out << "\t" << "\"step\": \"" << m_step << "\"," << endl;
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
    print_trace(out, m_var_list[0], 0, m_trajectory);
    for (size_t i = 1; i < m_var_list.size(); i++) {
        out << ", " << endl;
        print_trace(out, m_var_list[i], i, m_trajectory);
    }
    out << endl << "]" << endl;
}

void ode_solver::prune_trajectory(interval& time, IVector& e) {
    // Remove datapoints after time interval.
    auto ite = find_if (m_trajectory.begin(),
                        m_trajectory.end(),
                        [&time](pair<interval, IVector>& item) {
                            return item.first.leftBound() > time.rightBound();
                        });
    m_trajectory.erase(ite, m_trajectory.end());

    // Update the datapoints in the time interval
    ite = find_if (m_trajectory.begin(), m_trajectory.end(), [&time](pair<interval, IVector>& item) {
            return item.first.leftBound()>= time.leftBound();
        });
    for_each(ite, m_trajectory.end(), [&e](pair<interval, IVector>& item) {
            intersection(item.second, e, item.second);
        });
}

IVector ode_solver::varlist_to_IVector(vector<Enode*> const & vars) {
    IVector intvs (vars.size());
    /* Assign current interval values */
    for (unsigned i = 0; i < vars.size(); i++) {
        Enode* const & var = vars[i];
        interval & intv = intvs[i];
        double lb = get_lb(var);
        double ub = get_ub(var);
        intv = interval(lb, ub);
        DREAL_LOG_DEBUG("The interval on " << var->getCar()->getName() << ": " << intv);
    }
    return intvs;
}

IVector ode_solver::extract_invariants() {
    map<Enode*, pair<double, double>> inv_map;
    for (auto inv : m_invs) {
        Enode * p = inv->getCdr()->getCdr()->getCdr()->getCdr()->getCar();
        Enode * op = p->getCar();
        bool pos = true;

        // Handle Negation
        if (op->getId() == ENODE_ID_NOT) {
            p = p->getCdr()->getCar();
            op = p->getCar();
            pos = false;
        }
        switch (op->getId()) {
        case ENODE_ID_GEQ:
        case ENODE_ID_GT:
            // Handle >= & >
            pos = !pos;
        case ENODE_ID_LEQ:
        case ENODE_ID_LT: {
            // Handle <= & <
            Enode * lhs = pos ? p->getCdr()->getCar() : p->getCdr()->getCdr()->getCar();
            Enode * rhs = pos ? p->getCdr()->getCdr()->getCar() : p->getCdr()->getCar();
            if (lhs->isVar() && rhs->isConstant()) {
                if (inv_map.find(lhs) != inv_map.end()) {
                    inv_map[lhs].second = rhs->getValue();
                } else {
                    inv_map.emplace(lhs, make_pair(lhs->getLowerBound(), rhs->getValue()));
                }
            } else if (lhs->isConstant() && rhs->isVar()) {
                if (inv_map.find(rhs) != inv_map.end()) {
                    inv_map[rhs].first = lhs->getValue();
                } else {
                    inv_map.emplace(rhs, make_pair(lhs->getValue(), rhs->getUpperBound()));
                }
            } else {
                cerr << "ode_solver::extract_invariant: error:" << p << endl;
            }
        }
            break;
        default:
            cerr << "ode_solver::extract_invariant: error" << p << endl;
        }
    }
    IVector ret (m_t_vars.size());
    unsigned i = 0;
    for (auto const & m_t_var : m_t_vars) {
        if (inv_map.find(m_t_var) != inv_map.end()) {
            auto inv = interval(inv_map[m_t_var].first, inv_map[m_t_var].second);
            DREAL_LOG_DEBUG("Invariant extracted from  " << m_t_var << " = " << inv);
            ret[i++] = inv;
        } else {
            auto inv = interval(m_t_var->getLowerBound(), m_t_var->getUpperBound());
            DREAL_LOG_DEBUG("Default Invariant set for " << m_t_var << " = " << inv);
            ret[i++] = inv;
        }
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
    DREAL_LOG_DEBUG("  dt = " << dt);
    DREAL_LOG_DEBUG("time = " << time);
    if (dt.leftBound() > time.rightBound() || time.leftBound() > dt.rightBound()) {
        DREAL_LOG_DEBUG("IS " << "NOT CANDIDATE (TIME)");
        return;
    }
    for (auto i = 0; i < v.dimension(); i++) {
        DREAL_LOG_DEBUG("  v[" << i << ", " << _t_vars[i] << "] = " << v[i]);
        DREAL_LOG_DEBUG("x_t[" << i << ", " << _t_vars[i] << "] = " << "[" << get_lb(_t_vars[i]) << ", " << get_ub(_t_vars[i]) << "]");
        if ((v[i].leftBound() > get_ub(_t_vars[i])) || (v[i].rightBound() < get_lb(_t_vars[i]))) {
            DREAL_LOG_DEBUG("IS " << "NOT CANDIDATE (" << i << ")");
            return;
        }
    }
    DREAL_LOG_DEBUG("IS " << "CANDIDATE");
    v_bucket.push_back(v);
    time_bucket.push_back(dt);
}

bool ode_solver::simple_ODE(rp_box b, bool forward) {
    update(b);
    if (forward) {
        return simple_ODE_forward(m_X_0, m_X_t, m_T, m_inv, m_funcs);
    } else {
        return simple_ODE_backward(m_X_0, m_X_t, m_T, m_inv, m_funcs);
    }
}

bool ode_solver::solve_forward(rp_box b) {
    clock_t start_clock = clock();
    DREAL_LOG_DEBUG("ODE_Solver::solve_forward()");
    update(b);
    bool ret = true;
    IMap vectorField(m_diff_sys_forward);
    for (Enode * par : m_pars) {
        double lb = get_lb(par);
        double ub = get_ub(par);
        string name = par->getCar()->getName();
        vectorField.setParameter(name, interval(lb, ub));
    }
    ITaylor solver(vectorField, m_config.nra_ODE_taylor_order, .001);
    ITimeMap timeMap(solver);
    C0Rect2Set s(m_X_0);
    DREAL_LOG_INFO("interval T = " << m_T);
    timeMap.stopAfterStep(true);
    bool fastForward = false;
    timeMap.turnOnStepControl();
    interval prevTime(0.);
    if (m_config.nra_json) {
        m_trajectory.clear();
        m_trajectory.push_back(make_pair(timeMap.getCurrentTime(), IVector(s)));
    }
    vector<IVector> v_bucket;
    vector<interval> time_bucket;
    bool invariantViolated = false;

    clock_t end_clock;
    double elapsed_msecs;
    do {
        if (m_config.nra_ODE_timeout > 0.0) {
            end_clock = clock();
            elapsed_msecs = (static_cast<double>(end_clock) - static_cast<double>(start_clock)) * 1000 / CLOCKS_PER_SEC;
            if (elapsed_msecs >= m_config.nra_ODE_timeout) {
                DREAL_LOG_INFO("ODE_Solver::solve_forward() -- timeout : " << elapsed_msecs << "\t" << m_config.nra_ODE_timeout);
                ret = true;
                return ret;
            }
        }

        invariantViolated = !check_invariant(s, m_inv);
        timeMap.turnOnStepControl();
        if (m_stepControl > 0 && solver.getStep() < m_stepControl) {
            timeMap.turnOffStepControl();
            solver.setStep(m_stepControl);
            timeMap.setStep(m_stepControl);
        }

        timeMap(m_T.rightBound(), s);
        if (contain_NaN(s)) { return true; }
        DREAL_LOG_DEBUG("T : " << m_T);
        DREAL_LOG_DEBUG("currentTime : " << timeMap.getCurrentTime());
        if (!fastForward || m_T.leftBound() <= timeMap.getCurrentTime().rightBound()) {
            invariantViolated = inner_loop_forward(solver, prevTime, v_bucket, time_bucket);
        } else {
            DREAL_LOG_DEBUG("Fast-forward:: " << prevTime << " ===> " << timeMap.getCurrentTime());
            DREAL_LOG_DEBUG("enclosure for t=" << timeMap.getCurrentTime() << ": " << IVector(s));
        }
        prevTime = timeMap.getCurrentTime();
        DREAL_LOG_DEBUG("current time: " << prevTime);
        DREAL_LOG_DEBUG("InvViolated : " << invariantViolated << "timeMap.completed: " << timeMap.completed());
    } while (!invariantViolated && !timeMap.completed());
    if (union_and_join(v_bucket, m_X_t)) {
        IVector_to_varlist(m_X_t, m_t_vars);
    } else {
        for (auto _t_var : m_t_vars) {
            set_empty_interval(_t_var);
        }
        ret = false;
    }
    if (union_and_join(time_bucket, m_T)) {
        set_lb(m_time, m_T.leftBound());
        set_ub(m_time, m_T.rightBound());
    } else {
        set_empty_interval(m_time);
        ret = false;
    }
    if (m_config.nra_json) {
        prune_trajectory(m_T, m_X_t);
    }
    return ret;
}

bool ode_solver::solve_backward(rp_box b) {
    clock_t start_clock = clock();
    DREAL_LOG_DEBUG("ODE_Solver::solve_backward()");
    update(b);
    bool ret = true;
    IMap vectorField(m_diff_sys_backward);
    for (Enode * par : m_pars) {
        double lb = get_lb(par);
        double ub = get_ub(par);
        string name = par->getCar()->getName();
        vectorField.setParameter(name, interval(lb, ub));
    }
    ITaylor solver(vectorField, m_config.nra_ODE_taylor_order, .001);
    ITimeMap timeMap(solver);
    C0Rect2Set s(m_X_t);
    DREAL_LOG_INFO("interval T = " << m_T);
    timeMap.stopAfterStep(true);
    bool fastForward = false;
    timeMap.turnOnStepControl();
    interval prevTime(0.);
    if (m_config.nra_json) {
        m_trajectory.clear();
        m_trajectory.push_back(make_pair(m_T.rightBound() - timeMap.getCurrentTime(), IVector(s)));
    }
    vector<IVector> v_bucket;
    vector<interval> time_bucket;
    bool invariantViolated = false;

    clock_t end_clock;
    double elapsed_msecs;
    do {
        if (m_config.nra_ODE_timeout > 0.0) {
            end_clock = clock();
            elapsed_msecs = (static_cast<double>(end_clock) - static_cast<double>(start_clock)) * 1000 / CLOCKS_PER_SEC;
            if (elapsed_msecs >= m_config.nra_ODE_timeout) {
                DREAL_LOG_INFO("ODE_Solver::solve_backward() -- timeout : " << elapsed_msecs << "\t" << m_config.nra_ODE_timeout);
                ret = true;
                return ret;
            }
        }

        invariantViolated = !check_invariant(s, m_inv);
        // timeMap.turnOnStepControl();
        if (m_stepControl > 0 && solver.getStep() < m_stepControl) {
            timeMap.turnOffStepControl();
            solver.setStep(m_stepControl);
            timeMap.setStep(m_stepControl);
        }

        timeMap(m_T.rightBound(), s);
        if (contain_NaN(s)) { return true; }
        DREAL_LOG_DEBUG("T : " << m_T);
        DREAL_LOG_DEBUG("currentTime : " << timeMap.getCurrentTime());
        if (!fastForward || m_T.leftBound() <= timeMap.getCurrentTime().rightBound()) {
            invariantViolated = inner_loop_backward(solver, prevTime, v_bucket, time_bucket);
        } else {
            DREAL_LOG_DEBUG("Fast-forward:: " << prevTime << " ===> " << timeMap.getCurrentTime());
            DREAL_LOG_DEBUG("enclosure for t=" << timeMap.getCurrentTime() << ": " << IVector(s));
        }
        prevTime = timeMap.getCurrentTime();
        DREAL_LOG_DEBUG("current time: " << prevTime);
        DREAL_LOG_DEBUG("InvViolated : " << invariantViolated);
        DREAL_LOG_DEBUG("timeMap.completed: " << timeMap.completed());
    } while (!invariantViolated && !timeMap.completed());
    if (union_and_join(v_bucket, m_X_0)) {
        IVector_to_varlist(m_X_0, m_0_vars);
    } else {
        for (auto _0_var : m_0_vars) {
            set_empty_interval(_0_var);
        }
        ret = false;
    }
    if (union_and_join(time_bucket, m_T)) {
        set_lb(m_time, m_T.leftBound());
        set_ub(m_time, m_T.rightBound());
    } else {
        set_empty_interval(m_time);
        ret = false;
    }
    if (m_config.nra_json) {
        prune_trajectory(m_T, m_X_0);
    }

    // Reverse trajectory vector
    reverse(m_trajectory.begin(), m_trajectory.end());
    return ret;
}

bool ode_solver::check_invariant(IVector & v, IVector const & inv) {
    if (!intersection(v, inv, v)) {
        if (m_config.nra_verbose) {
            DREAL_LOG_DEBUG("invariant violated!");
            for (auto i = 0; i < v.dimension(); i++) {
                if (v[i].leftBound() < inv[i].leftBound() || v[i].rightBound() > inv[i].rightBound()) {
                    DREAL_LOG_DEBUG("inv[" << i << "] = " << inv[i]);
                    DREAL_LOG_DEBUG("  v[" << i << "] = " <<   v[i]);
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
            DREAL_LOG_DEBUG("NaN Found! : " << v);
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
        DREAL_LOG_DEBUG("Union_Join: collect from the bucket");
        return false;
    }
    V u = *(bucket.cbegin());
    for (auto ite = ++(bucket.cbegin()); ite != bucket.cend(); ite++) {
        DREAL_LOG_DEBUG("U(" << u << ", " << *ite << ")");
        u = intervalHull(u, *ite);
        DREAL_LOG_DEBUG(" = " << u);
    }
    // 2. result = intersection(u, result);
    DREAL_LOG_DEBUG("Intersect(" << u << ", " << result << ")");
    if (intersection(u, result, result)) {
        DREAL_LOG_DEBUG(" = " << result);
    } else {
        // intersection is empty!!
        DREAL_LOG_DEBUG(" = empty");
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
    for (unsigned i = 0; i <m_config.nra_ODE_grid_size; i++) {
        interval subsetOfDomain = domain / m_config.nra_ODE_grid_size
            + (domainWidth / m_config.nra_ODE_grid_size) * i;
        intersection(domain, subsetOfDomain, subsetOfDomain);
        IVector v = curve(subsetOfDomain);
        DREAL_LOG_DEBUG("subsetOfDomain: " << subsetOfDomain);
        DREAL_LOG_DEBUG("enclosure for t=" << prevTime + subsetOfDomain << ": " << v);
        DREAL_LOG_DEBUG("diam(enclosure): " << diam(v));
        if (!check_invariant(v, m_inv)) {
            return true;
        }
        DREAL_LOG_DEBUG("inv = " << m_inv);
        DREAL_LOG_DEBUG("v = " << v);
        DREAL_LOG_DEBUG("enclosure for t intersected with inv " << prevTime + subsetOfDomain << ": " << v);
        prune(m_t_vars, v, prevTime + subsetOfDomain, m_T, v_bucket, time_bucket);
        if (m_config.nra_json) {
            m_trajectory.push_back(make_pair(prevTime + subsetOfDomain, v));
        }
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
    for (unsigned i = 0; i < m_config.nra_ODE_grid_size; i++) {
        interval subsetOfDomain = domain / m_config.nra_ODE_grid_size
            + (domainWidth / m_config.nra_ODE_grid_size) * i;
        intersection(domain, subsetOfDomain, subsetOfDomain);
        IVector v = curve(subsetOfDomain);
        DREAL_LOG_DEBUG("subsetOfDomain: " << subsetOfDomain);
        DREAL_LOG_DEBUG("enclosure for t=" << prevTime + subsetOfDomain << ": " << v);
        DREAL_LOG_DEBUG("diam(enclosure): " << diam(v));
        if (!check_invariant(v, m_inv)) {
            return true;
        }
        DREAL_LOG_DEBUG("inv = " << m_inv);
        DREAL_LOG_DEBUG("v = " << v);
        DREAL_LOG_DEBUG("enclosure for t intersected with inv " << prevTime + subsetOfDomain << ": " << v);
        prune(m_0_vars, v, prevTime + subsetOfDomain, m_T, v_bucket, time_bucket);
        if (m_config.nra_json) {
            m_trajectory.push_back(make_pair(m_T.rightBound() - (prevTime + subsetOfDomain), v));
        }
    }
    return false;
}

bool ode_solver::simple_ODE_forward(IVector const & X_0, IVector & X_t, interval const & T,
                                    IVector const & inv, vector<IFunction> & funcs) {
    // X_t = X_t \cup (X_0 + (d/dt Inv) * T)
    for (int i = 0; i < X_0.dimension(); i++) {
        interval const & x_0 = X_0[i];
        interval & x_t = X_t[i];
        IFunction & dxdt = funcs[i];

        for (Enode * par : m_pars) {
            double lb = get_lb(par);
            double ub = get_ub(par);
            string name = par->getCar()->getName();
            dxdt.setParameter(name, interval(lb, ub));
        }

        try {
            interval new_x_t = x_0 + dxdt(inv) * T;
            if (!intersection(new_x_t, x_t, x_t)) {
                DREAL_LOG_DEBUG("Simple_ODE: no intersection for X_T");
                return false;
            }
        } catch (exception& e) {
            DREAL_LOG_DEBUG("Exception in Simple_ODE: " << e.what());
        }
    }
    // update
    IVector_to_varlist(X_t, m_t_vars);
    return true;
}

bool ode_solver::simple_ODE_backward(IVector & X_0, IVector const & X_t, interval const & T,
                                     IVector const & inv, vector<IFunction> & funcs) {
    // X_0 = X_0 \cup (X_t - + (d/dt Inv) * T)
    for (int i = 0; i < X_0.dimension(); i++) {
        interval & x_0 = X_0[i];
        interval const & x_t = X_t[i];
        IFunction & dxdt = funcs[i];

        for (Enode * par : m_pars) {
            double lb = get_lb(par);
            double ub = get_ub(par);
            string name = par->getCar()->getName();
            dxdt.setParameter(name, interval(lb, ub));
        }

        try {
            interval const new_x_0 = x_t - dxdt(inv) * T;
            if (!intersection(new_x_0, x_0, x_0)) {
                DREAL_LOG_DEBUG("Simple_ODE: no intersection for X_0");
                return false;
            }
        } catch (exception& e) {
            DREAL_LOG_DEBUG("Exception in Simple_ODE: " << e.what());
        }
    }
    // update
    IVector_to_varlist(X_0, m_0_vars);
    return true;
}

double ode_solver::logVolume_X0(rp_box b) const {
    double ret = 0;
    for (Enode * var : m_0_vars) {
        double const lb = rp_binf(rp_box_elem(b, m_enode_to_rp_id[var]));
        double const ub = rp_bsup(rp_box_elem(b, m_enode_to_rp_id[var]));
        double const s = max(ub - lb, m_config.nra_precision);
        ret += log(s);
    }
    return ret;
}
double ode_solver::logVolume_Xt(rp_box b) const {
    double ret = 0;
    for (Enode * var : m_t_vars) {
        double const lb = rp_binf(rp_box_elem(b, m_enode_to_rp_id[var]));
        double const ub = rp_bsup(rp_box_elem(b, m_enode_to_rp_id[var]));
        double const s = max(ub - lb, m_config.nra_precision);
        ret += log(s);
    }
    return ret;
}

vector<double> ode_solver::extractX0T(rp_box b) const {
    vector<double> ret;
    ret.emplace_back(m_mode); // Mode
    // Time
    ret.emplace_back(rp_binf(rp_box_elem(b, m_enode_to_rp_id[m_time])));
    ret.emplace_back(rp_bsup(rp_box_elem(b, m_enode_to_rp_id[m_time])));

    // X_0
    for (Enode * var : m_0_vars) {
        ret.emplace_back(rp_binf(rp_box_elem(b, m_enode_to_rp_id[var])));
        ret.emplace_back(rp_bsup(rp_box_elem(b, m_enode_to_rp_id[var])));
    }
    return ret;
}

vector<double> ode_solver::extractXtT(rp_box b) const {
    vector<double> ret;
    ret.emplace_back(m_mode); // Mode
    // Time
    ret.emplace_back(rp_binf(rp_box_elem(b, m_enode_to_rp_id[m_time])));
    ret.emplace_back(rp_bsup(rp_box_elem(b, m_enode_to_rp_id[m_time])));

    // X_t
    for (Enode * var : m_t_vars) {
        ret.emplace_back(rp_binf(rp_box_elem(b, m_enode_to_rp_id[var])));
        ret.emplace_back(rp_bsup(rp_box_elem(b, m_enode_to_rp_id[var])));
    }
    return ret;
}

vector<double> ode_solver::extractX0XtT(rp_box b) const {
    vector<double> ret;
    ret.emplace_back(m_mode); // Mode
    // Time
    ret.emplace_back(rp_binf(rp_box_elem(b, m_enode_to_rp_id[m_time])));
    ret.emplace_back(rp_bsup(rp_box_elem(b, m_enode_to_rp_id[m_time])));

    // X_0
    for (Enode * var : m_0_vars) {
        ret.emplace_back(rp_binf(rp_box_elem(b, m_enode_to_rp_id[var])));
        ret.emplace_back(rp_bsup(rp_box_elem(b, m_enode_to_rp_id[var])));
    }

    // X_t
    for (Enode * var : m_t_vars) {
        ret.emplace_back(rp_binf(rp_box_elem(b, m_enode_to_rp_id[var])));
        ret.emplace_back(rp_bsup(rp_box_elem(b, m_enode_to_rp_id[var])));
    }
    return ret;
}
