/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@mit.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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

#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <deque>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "constraint/constraint.h"
#include "ibex/ibex.h"
#include "interval/interval.icc"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/flow.h"
#include "util/ibex_enode.h"
#include "util/logging.h"

using std::cerr;
using std::copy;
using std::endl;
using std::initializer_list;
using std::isfinite;
using std::logic_error;
using std::make_pair;
using std::make_shared;
using std::map;
using std::numeric_limits;
using std::ostream;
using std::pair;
using std::shared_ptr;
using std::string;
using std::thread;
using std::to_string;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {

ostream & operator<<(ostream & out, constraint_type const & ty) {
    switch (ty) {
        case constraint_type::Nonlinear:
            out << "Nonlinear";
            break;
        case constraint_type::ODE:
            out << "ODE";
            break;
        case constraint_type::Integral:
            out << "Integral";
            break;
        case constraint_type::ForallT:
            out << "ForallT";
            break;
        case constraint_type::Exists:
            out << "Exists";
            break;
        case constraint_type::Forall:
            out << "Forall";
            break;
    }
    return out;
}

// ====================================================
// constraint
// ====================================================
constraint::constraint(constraint_type ty) : m_type(ty) {}
ostream & operator<<(ostream & out, constraint const & c) { return c.display(out); }

// ====================================================
// Nonlinear constraint
// ====================================================

void nonlinear_constraint::build_maps() const {
    std::thread::id const tid = std::this_thread::get_id();
    assert(m_numctr_map.find(tid) == m_numctr_map.cend());
    assert(m_var_array_map.find(tid) == m_var_array_map.cend());
    // Build var_array_map
    map<string, ibex::ExprSymbol const *> var_map = build_var_map(m_domain_vars);
    ibex::Array<ibex::ExprSymbol const> & var_array = m_var_array_map[tid];
    var_array.resize(var_map.size());
    int i = 0;
    for (auto const item : var_map) {
        var_array.set_ref(i++, *(item.second));
    }
    // The use of unique_ptr is to free the returned exprctr* from translate_enode_to_exprctr
    unique_ptr<ibex::ExprCtr const> exprctr(
        translate_enode_to_exprctr(var_map, get_enode(), m_polarity, m_subst));
    m_numctr_map[tid].reset(new ibex::NumConstraint(var_array, *exprctr));
}

shared_ptr<ibex::NumConstraint> const & nonlinear_constraint::get_numctr() const {
    std::thread::id const tid = std::this_thread::get_id();
    std::lock_guard<std::mutex> lock(m_map_lock);
    unordered_map<thread::id, shared_ptr<ibex::NumConstraint>>::const_iterator const it =
        m_numctr_map.find(tid);
    if (it != m_numctr_map.cend()) {
        return it->second;
    } else {
        build_maps();
        return m_numctr_map[tid];
    }
}

ibex::Array<ibex::ExprSymbol const> const & nonlinear_constraint::get_var_array() const {
    std::thread::id const tid = std::this_thread::get_id();
    std::lock_guard<std::mutex> lock(m_map_lock);
    unordered_map<thread::id, ibex::Array<ibex::ExprSymbol const>>::const_iterator const it =
        m_var_array_map.find(tid);
    if (it != m_var_array_map.cend()) {
        return it->second;
    } else {
        build_maps();
        return m_var_array_map[tid];
    }
}

nonlinear_constraint::nonlinear_constraint(Enode * const e,
                                           unordered_set<Enode *> const & domain_vars,
                                           lbool const p,
                                           unordered_map<Enode *, ibex::Interval> const & subst)
    : constraint(constraint_type::Nonlinear),
      m_enode(e),
      m_polarity(p),
      m_domain_vars(domain_vars),
      m_subst(subst) {
    build_maps();
}

ostream & nonlinear_constraint::display(ostream & out) const {
    out << "nonlinear_constraint ";
    if (is_neq()) {
        out << "!(" << *get_numctr() << ")";
    } else {
        out << *get_numctr();
    }
    return out;
}

ostream & nonlinear_constraint::display_dr(ostream & out) const {
    if (is_neq()) {
        out << "(not " << *get_numctr() << ")";
    } else {
        out << *get_numctr();
    }
    return out;
}

pair<lbool, ibex::Interval> nonlinear_constraint::eval(ibex::IntervalVector const & iv) const {
    lbool sat = l_Undef;
    ibex::Interval result;
    if (!is_neq()) {
        result = get_numctr()->f.eval(iv);
        switch (get_numctr()->op) {
            case ibex::LT:
                if (result.ub() < 0) {
                    //    [         ]
                    // --------------- 0 --------------
                    sat = l_True;
                } else if (0 <= result.lb()) {
                    //                 [         ]
                    // --------------- 0 --------------
                    sat = l_False;
                }
                break;
            case ibex::LEQ:
                if (result.ub() <= 0) {
                    //       [         ]
                    // --------------- 0 --------------
                    sat = l_True;
                } else if (0 < result.lb()) {
                    //                   [         ]
                    // --------------- 0 --------------
                    sat = l_False;
                }
                break;
            case ibex::GT:
                if (0 < result.lb()) {
                    //                   [         ]
                    // --------------- 0 --------------
                    sat = l_True;
                } else if (result.ub() <= 0) {
                    //       [         ]
                    // --------------- 0 --------------
                    sat = l_False;
                }
                break;
            case ibex::GEQ:
                if (0 <= result.lb()) {
                    //                 [         ]
                    // --------------- 0 --------------
                    sat = l_True;
                } else if (result.ub() < 0) {
                    //     [         ]
                    // --------------- 0 --------------
                    sat = l_False;
                }
                break;
            case ibex::EQ:
                if (result.lb() == 0 && result.ub() == 0) {
                    //                 x
                    // --------------- 0 --------------
                    sat = l_True;
                } else if ((result.ub() < 0) || (0 < result.lb())) {
                    //  [            ] | [            ]
                    // --------------- 0 --------------
                    sat = l_False;
                }
                break;
        }
    } else {
        // NEQ case: lhs - rhs != 0
        result = get_numctr()->f.eval(iv);
        if ((result.lb() == 0) && (result.ub() == 0)) {
            //     [      lhs      ]
            //     [      rhs      ]
            sat = l_False;
        } else {
            sat = l_True;
        }
    }
    if (DREAL_LOG_DEBUG_IS_ON && sat == l_False) {
        DREAL_LOG_DEBUG << "nonlinear_constraint::eval: unsat detected";
        DREAL_LOG_DEBUG << "\t" << *this;
        DREAL_LOG_DEBUG << "input: " << iv;
        DREAL_LOG_DEBUG << "output:" << result;
    }
    return make_pair(sat, result);
}

double nonlinear_constraint::eval_error(ibex::IntervalVector const & iv) const {
    ibex::Interval eval_result;
    double result = 0.0;
    double const magic_num = numeric_limits<double>::max() / 1.5;
    if (!is_neq()) {
        eval_result = get_numctr()->f.eval(iv);
        switch (get_numctr()->op) {
            case ibex::LT:
                result = eval_result.ub() < 0.0 ? 0.0 : fabs(eval_result.ub());
                break;
            case ibex::LEQ:
                result = eval_result.ub() <= 0.0 ? 0.0 : fabs(eval_result.ub());
                break;
            case ibex::GT:
                result = eval_result.lb() > 0.0 ? 0.0 : fabs(eval_result.lb());
                break;
            case ibex::GEQ:
                result = eval_result.lb() >= 0.0 ? 0.0 : fabs(eval_result.lb());
                break;
            case ibex::EQ:
                result = fabs(eval_result.ub());
                break;
        }
        // if result is not finite then return the magic number
        if (!isfinite(result)) {
            result = magic_num;
        }
    } else {
        // trivialize neq
        result = 0.0;
    }
    if (DREAL_LOG_DEBUG_IS_ON) {
        DREAL_LOG_DEBUG << "nonlinear_constraint::eval_error:";
        DREAL_LOG_DEBUG << "\t" << *this;
        DREAL_LOG_DEBUG << "input: " << iv;
        DREAL_LOG_DEBUG << "output:" << result;
    }
    assert(result >= 0.0);
    return result;
}

pair<lbool, ibex::Interval> nonlinear_constraint::eval(box const & b) const {
    // Construct iv from box b
    if (get_var_array().size() > 0) {
        ibex::IntervalVector iv(get_var_array().size());
        for (int i = 0; i < get_var_array().size(); i++) {
            iv[i] = b[get_var_array()[i].name];
            DREAL_LOG_DEBUG << get_var_array()[i].name << " = " << iv[i];
        }
        return eval(iv);
    } else {
        ibex::IntervalVector iv(1);
        return eval(iv);
    }
}

double nonlinear_constraint::eval_error(box const & b) const {
    // Construct iv from box b
    if (get_var_array().size() > 0) {
        ibex::IntervalVector iv(get_var_array().size());
        for (int i = 0; i < get_var_array().size(); i++) {
            iv[i] = b[get_var_array()[i].name];
            DREAL_LOG_DEBUG << get_var_array()[i].name << " = " << iv[i];
        }
        return eval_error(iv);
    } else {
        ibex::IntervalVector iv(1);
        return eval_error(iv);
    }
}

// ====================================================
// ODE constraint
// ====================================================
ode_constraint::ode_constraint(integral_constraint const & integral,
                               vector<shared_ptr<forallt_constraint>> const & invs)
    : constraint(constraint_type::ODE), m_int(integral), m_invs(invs) {}

vector<Enode *> ode_constraint::get_enodes() const {
    if (m_invs.empty()) {
        return {m_int.get_enode()};
    } else {
        vector<Enode *> ret{m_int.get_enode()};
        for (shared_ptr<forallt_constraint> const inv : m_invs) {
            ret.push_back(inv->get_enode());
        }
        return ret;
    }
}

std::unordered_set<Enode *> ode_constraint::get_occured_vars() const {
    if (m_invs.empty()) {
        return m_int.get_occured_vars();
    } else {
        unordered_set<Enode *> ret{m_int.get_occured_vars()};
        for (shared_ptr<forallt_constraint> const inv : m_invs) {
            auto const occured_vars_in_inv = inv->get_occured_vars();
            ret.insert(occured_vars_in_inv.begin(), occured_vars_in_inv.end());
        }
        return ret;
    }
}

ostream & ode_constraint::display(ostream & out) const {
    out << "ode_constraint(" << m_int << ")" << endl;
    for (shared_ptr<forallt_constraint> const & inv : m_invs) {
        Enode * const e = inv->get_enode();
        if (e->hasPolarity() && e->getPolarity() == l_True) {
            out << *inv << endl;
        }
    }
    return out;
}

// ====================================================
// Integral constraint
// ====================================================
integral_constraint mk_integral_constraint(Enode * const e,
                                           unordered_map<string, flow> const & flow_map) {
    // nra_solver::inform: (integral 2 0 time_9 v_9_0 v_9_t x_9_0 x_9_t)
    Enode const * tmp = e->getCdr();
    unsigned flow_id = tmp->getCar()->getValue();
    tmp = tmp->getCdr();

    Enode * const time_0 = tmp->getCar();
    tmp = tmp->getCdr();

    Enode * const time_t = tmp->getCar();
    tmp = tmp->getCdr();

    string key = string("flow_") + to_string(flow_id);
    auto const it = flow_map.find(key);
    if (it == flow_map.end()) {
        throw logic_error(key + " is not in flow_map. Failed to create integral constraint");
    }
    flow const & _flow = it->second;
    vector<Enode *> const & flow_vars = _flow.get_vars();
    vector<Enode *> const & flow_odes = _flow.get_odes();
    vector<Enode *> vars_0, vars_t, pars_0, pars_t;
    vector<Enode *> par_lhs_names;
    vector<pair<Enode *, Enode *>> odes;

    for (unsigned i = 0; i < flow_vars.size(); i++) {
        Enode * const var_0 = tmp->getCar();
        tmp = tmp->getCdr();
        Enode * const var_t = tmp->getCar();
        tmp = tmp->getCdr();
        Enode * const ode_var = flow_vars[i];
        Enode * const ode_rhs = flow_odes[i];

        if (ode_rhs->isConstant() && ode_rhs->getValue() == 0.0) {
            // Parameter
            pars_0.push_back(var_0);
            pars_t.push_back(var_t);
            par_lhs_names.push_back(ode_var);
        } else {
            // Variable
            vars_0.push_back(var_0);
            vars_t.push_back(var_t);
            odes.emplace_back(ode_var, ode_rhs);
        }
    }
    if (!tmp->isEnil()) {
        DREAL_LOG_FATAL << "We found a problem in handling: " << e;
        DREAL_LOG_FATAL << "You provided " << flow_vars.size()
                        << " differential equation(s) in the system:";
        for (unsigned i = 0; i < flow_vars.size(); i++) {
            DREAL_LOG_FATAL << "\t"
                            << "d/dt[" << flow_vars[i] << "] = " << flow_odes[i];
        }
        DREAL_LOG_FATAL << "However, there are " << (flow_vars.size() + tmp->getSize())
                        << " pairs of variables shown:";
        tmp = e->getCdr()->getCdr()->getCdr()->getCdr();
        while (!tmp->isEnil()) {
            DREAL_LOG_FATAL << "\t" << tmp->getCar() << ", " << tmp->getCdr()->getCar();
            tmp = tmp->getCdr()->getCdr();
        }
        abort();
    }
    return integral_constraint(e, flow_id, time_0, time_t, vars_0, pars_0, vars_t, pars_t,
                               par_lhs_names, odes);
}

integral_constraint::integral_constraint(Enode * const e, int const flow_id, Enode * const time_0,
                                         Enode * const time_t, vector<Enode *> const & vars_0,
                                         vector<Enode *> const & pars_0,
                                         vector<Enode *> const & vars_t,
                                         vector<Enode *> const & pars_t,
                                         vector<Enode *> const & par_lhs_names,
                                         vector<pair<Enode *, Enode *>> const & odes)
    : constraint(constraint_type::Integral),
      m_enode(e),
      m_flow_id(flow_id),
      m_time_0(time_0),
      m_time_t(time_t),
      m_vars_0(vars_0),
      m_pars_0(pars_0),
      m_vars_t(vars_t),
      m_pars_t(pars_t),
      m_par_lhs_names(par_lhs_names),
      m_odes(odes) {}
ostream & integral_constraint::display(ostream & out) const {
    out << "integral_constraint = " << get_enode() << endl;
    out << "\t"
        << "flow_id = " << m_flow_id << endl;
    out << "\t"
        << "time = [" << m_time_0 << "," << m_time_t << "]" << endl;
    for (unsigned i = 0; i < m_pars_0.size(); ++i) {
        out << "\t"
            << "par: " << m_pars_0[i] << " " << m_pars_t[i] << endl;
    }
    for (unsigned i = 0; i < m_vars_0.size(); ++i) {
        out << "\t"
            << "var: " << m_vars_0[i] << " " << m_vars_t[i] << endl;
    }
    for (auto const & ode : m_odes) {
        out << "\t"
            << "d/dt[" << ode.first << "] = " << ode.second << endl;
    }
    return out;
}

// ====================================================
// ForallT constraint
// ====================================================

vector<shared_ptr<nonlinear_constraint>> make_nlctrs(Enode * const e,
                                                     unordered_set<Enode *> const & var_set,
                                                     lbool const p) {
    vector<shared_ptr<nonlinear_constraint>> ret;
    if (e->isTrue()) {
        return ret;
    }
    if (e->isFalse()) {
        DREAL_LOG_FATAL << "false is not a valid invariant (forall_t constraint)";
        throw logic_error("false is not a valid invariant (forall_t constraint)");
    }
    if (e->isNot()) {
        return make_nlctrs(e->get1st(), var_set, !p);
    }
    if (e->isAnd()) {
        Enode * tmp = e->getCdr();
        while (!tmp->isEnil()) {
            auto const nlctrs = make_nlctrs(e->get1st(), var_set, p);
            ret.insert(ret.end(), nlctrs.begin(), nlctrs.end());
            tmp = tmp->getCdr();
        }
        return ret;
    }
    if (e->isOr()) {
        DREAL_LOG_FATAL << "or is not a valid invariant for now, (forall_t constraint)";
        throw logic_error("false is not a valid invariant for now, (forall_t constraint)");
    }
    ret.push_back(make_shared<nonlinear_constraint>(e, var_set, p));
    return ret;
}

forallt_constraint::forallt_constraint(Enode * const e, unordered_set<Enode *> const & var_set,
                                       int const flow_id, Enode * const time_0,
                                       Enode * const time_t, Enode * const inv)
    : constraint(constraint_type::ForallT),
      m_enode(e),
      m_flow_id(flow_id),
      m_time_0(time_0),
      m_time_t(time_t),
      m_inv(inv) {
    m_nl_ctrs = make_nlctrs(inv, var_set, l_True);
}
ostream & forallt_constraint::display(ostream & out) const {
    out << "forallt_constraint = " << get_enode() << endl;
    out << "\t"
        << "flow_id = " << m_flow_id << endl;
    out << "\t"
        << "time = [" << m_time_0 << "," << m_time_t << "]" << endl;
    out << "\t"
        << "inv : " << m_inv << endl;
    return out;
}

forallt_constraint mk_forallt_constraint(Enode * const e, unordered_set<Enode *> const & var_set) {
    // nra_solver::inform: (forallt 2 0 time_9 (<= 0 v_9_t))
    Enode const * tmp = e->getCdr();
    unsigned const flow_id = tmp->getCar()->getValue();
    tmp = tmp->getCdr();

    Enode * const time_0 = tmp->getCar();
    tmp = tmp->getCdr();

    Enode * const time_t = tmp->getCar();
    tmp = tmp->getCdr();

    Enode * const inv = tmp->getCar();
    return forallt_constraint(e, var_set, flow_id, time_0, time_t, inv);
}

// ====================================================
// Forall constraint
// ====================================================
unordered_set<Enode *> forall_constraint::extract_forall_vars(Enode const * elist) {
    unordered_set<Enode *> ret;
    while (!elist->isEnil()) {
        ret.insert(elist->getCar());
        elist = elist->getCdr();
    }
    return ret;
}

forall_constraint::forall_constraint(Enode * const e, lbool const p)
    : constraint(constraint_type::Forall),
      m_enode(e),
      m_forall_vars(extract_forall_vars(e->getCdr()->getCdr())),
      m_body(e->getCdr()->getCar()),
      m_polarity(p) {}

unordered_set<Enode *> forall_constraint::get_forall_vars() const { return m_forall_vars; }

Enode * forall_constraint::get_body() const { return m_body; }

ostream & forall_constraint::display(ostream & out) const {
    out << "forall([ ";
    for (Enode * const var : m_forall_vars) {
        out << var << " ";
    }
    out << "], " << (m_polarity == l_True ? "" : "!") << get_enode() << ")" << endl;
    return out;
}
}  // namespace dreal
