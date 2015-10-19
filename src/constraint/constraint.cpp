/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include <algorithm>
#include <initializer_list>
#include <iostream>
#include <iterator>
#include <map>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "opensmt/egraph/Enode.h"
#include "constraint/constraint.h"
#include "util/flow.h"
#include "util/ibex_enode.h"
#include "ibex/ibex_ExprCopy.h"
#include "util/logging.h"

using std::cerr;
using std::copy;
using std::endl;
using std::initializer_list;
using std::logic_error;
using std::make_pair;
using std::make_shared;
using std::map;
using std::ostream;
using std::pair;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::shared_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace std {
// Hash for nonlinear_constraint
size_t hash<dreal::nonlinear_constraint>::operator()(dreal::nonlinear_constraint const & ctr) const {
    return hash<uintptr_t>()(reinterpret_cast<uintptr_t>(ctr.get_numctr().get()));
}
}  // namespace std

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
    case constraint_type::GenericForall:
        out << "GenericForall";
        break;
    }
    return out;
}

// ====================================================
// constraint
// ====================================================
constraint::constraint(constraint_type ty) : m_type(ty) {
}
constraint::constraint(constraint_type ty, Enode * const e)
    : m_type(ty), m_enodes(1, e), m_vars(e->get_vars()) {
}

unordered_set<Enode *> build_vars_from_enodes(initializer_list<vector<Enode *>> const & enodes_list) {
    unordered_set<Enode *> ret;
    for (auto const & enodes : enodes_list) {
        for (auto const e : enodes) {
            unordered_set<Enode *> const & s = e->get_vars();
            ret.insert(s.begin(), s.end());
        }
    }
    return ret;
}

constraint::constraint(constraint_type ty, vector<Enode *> const & enodes)
    : m_type(ty), m_enodes(enodes), m_vars(build_vars_from_enodes({enodes})) {
}
constraint::constraint(constraint_type ty, vector<Enode *> const & enodes_1, vector<Enode *> const & enodes_2)
    : m_type(ty), m_enodes(enodes_1), m_vars(build_vars_from_enodes({enodes_1, enodes_2})) {
    m_enodes.insert(m_enodes.end(), enodes_2.begin(), enodes_2.end());
}
ostream & operator<<(ostream & out, constraint const & c) {
    return c.display(out);
}

// ====================================================
// Nonlinear constraint
// ====================================================
nonlinear_constraint::nonlinear_constraint(Enode * const e,
                                           unordered_set<Enode*> const & var_set,
                                           lbool const p, unordered_map<Enode*, ibex::Interval> const & subst)
    : constraint(constraint_type::Nonlinear, e), m_is_neq(p == l_False && e->isEq()),
      m_numctr(nullptr), m_var_array(var_set.size()) {
    // Build var_map and var_array
    // Need to pass a fresh copy of var_array everytime it builds NumConstraint
    auto var_map = build_var_map(var_set);
    m_var_array.resize(var_map.size());
    unsigned i = 0;
    for (auto const item : var_map) {
        m_var_array.set_ref(i++, item.second);
    }
    unique_ptr<ibex::ExprCtr const> exprctr(translate_enode_to_exprctr(var_map, e, p, subst));
    m_numctr.reset(new ibex::NumConstraint(m_var_array, *exprctr));
    DREAL_LOG_INFO << "nonlinear_constraint: "<< *this;
}

ostream & nonlinear_constraint::display(ostream & out) const {
    out << "nonlinear_constraint ";
    if (m_is_neq) {
        out << "!(" << *m_numctr << ")";
    } else {
        out << *m_numctr;
    }
    return out;
}

pair<lbool, ibex::Interval> nonlinear_constraint::eval(ibex::IntervalVector const & iv) const {
    lbool sat = l_Undef;
    ibex::Interval result;
    if (!m_is_neq) {
        result = m_numctr->f.eval(iv);
        switch (m_numctr->op) {
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
        result = m_numctr->f.eval(iv);
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

pair<lbool, ibex::Interval> nonlinear_constraint::eval(box const & b) const {
    // Construct iv from box b
    if (m_var_array.size() > 0) {
        ibex::IntervalVector iv(m_var_array.size());
        for (int i = 0; i < m_var_array.size(); i++) {
            iv[i] = b[m_var_array[i].name];
            DREAL_LOG_DEBUG << m_var_array[i].name << " = " << iv[i];
        }
        return eval(iv);
    } else {
        ibex::IntervalVector iv(1);
        return eval(iv);
    }
}

// ====================================================
// ODE constraint
// ====================================================
ode_constraint::ode_constraint(integral_constraint const & integral, vector<forallt_constraint> const & invs)
    : constraint(constraint_type::ODE, integral.get_enodes()), m_int(integral), m_invs(invs) {
    for (auto const & inv : invs) {
        m_enodes.insert(m_enodes.end(), inv.get_enodes().begin(), inv.get_enodes().end());
    }
}
ostream & ode_constraint::display(ostream & out) const {
    out << "ode_constraint" << endl;
    out << m_int << endl;
    for (forallt_constraint const & inv : m_invs) {
        out << inv << endl;
    }
    return out;
}

// ====================================================
// Integral constraint
// ====================================================
integral_constraint mk_integral_constraint(Enode * const e, unordered_map<string, flow> const & flow_map) {
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
    assert(tmp->isEnil());

    return integral_constraint(e, flow_id, time_0, time_t, vars_0, pars_0, vars_t, pars_t, par_lhs_names, odes);
}

integral_constraint::integral_constraint(Enode * const e, unsigned const flow_id, Enode * const time_0, Enode * const time_t,
                                         vector<Enode *> const & vars_0, vector<Enode *> const & pars_0,
                                         vector<Enode *> const & vars_t, vector<Enode *> const & pars_t,
                                         vector<Enode *> const & par_lhs_names,
                                         vector<pair<Enode *, Enode *>> const & odes)
    : constraint(constraint_type::Integral, e),
      m_flow_id(flow_id), m_time_0(time_0), m_time_t(time_t),
      m_vars_0(vars_0), m_pars_0(pars_0), m_vars_t(vars_t), m_pars_t(pars_t),
      m_par_lhs_names(par_lhs_names), m_odes(odes) { }
ostream & integral_constraint::display(ostream & out) const {
    out << "integral_constraint = " << m_enodes[0] << endl;
    out << "\t" << "flow_id = " << m_flow_id << endl;
    out << "\t" << "time = [" << m_time_0 << "," << m_time_t << "]" << endl;
    for (Enode * par_0 : m_pars_0) { out << "\t" << "par_0 : " << par_0 << endl; }
    for (Enode * par_t : m_pars_t) { out << "\t" << "par_t : " << par_t << endl; }
    for (Enode * var_0 : m_vars_0) { out << "\t" << "var_0 : " << var_0 << endl; }
    for (Enode * var_t : m_vars_t) { out << "\t" << "var_t : " << var_t << endl; }
    for (auto const & ode : m_odes) {
        out << "\t" << "d/dt[" << ode.first << "] = " << ode.second << endl;
    }
    return out;
}

// ====================================================
// ForallT constraint
// ====================================================

vector<shared_ptr<nonlinear_constraint>> make_nlctrs(Enode * const e,
unordered_set<Enode*> const & var_set, lbool const p) {
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
            auto const nlctrs = make_nlctrs(e->get1st(), var_set, !p);
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

forallt_constraint::forallt_constraint(Enode * const e, unordered_set<Enode*> const & var_set, unsigned const flow_id, Enode * const time_0, Enode * const time_t, Enode * const inv)
    : constraint(constraint_type::ForallT, e), m_flow_id(flow_id), m_time_0(time_0), m_time_t(time_t), m_inv(inv) {
    m_nl_ctrs = make_nlctrs(inv, var_set, l_True);
}
ostream & forallt_constraint::display(ostream & out) const {
    out << "forallt_constraint = " << m_enodes[0] << endl;
    out << "\t" << "flow_id = " << m_flow_id << endl;
    out << "\t" << "time = [" << m_time_0 << "," << m_time_t << "]" << endl;
    out << "\t" << "inv : " << m_inv << endl;
    return out;
}

forallt_constraint mk_forallt_constraint(Enode * const e, unordered_set<Enode*> const & var_set) {
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
// Generic Forall constraint
// ====================================================
unordered_set<Enode *> generic_forall_constraint::extract_forall_vars(Enode const * elist) {
    unordered_set<Enode *> ret;
    while (!elist->isEnil()) {
        ret.insert(elist->getCar());
        elist = elist->getCdr();
    }
    return ret;
}

generic_forall_constraint::generic_forall_constraint(Enode * const e, lbool const p)
    : constraint(constraint_type::GenericForall, e),
      m_forall_vars(extract_forall_vars(e->getCdr()->getCdr())),
      m_body(e->getCdr()->getCar()),
      m_polarity(p) {
}
unordered_set<Enode *> generic_forall_constraint::get_forall_vars() const {
    return m_forall_vars;
}
Enode * generic_forall_constraint::get_body() const {
    return m_body;
}
ostream & generic_forall_constraint::display(ostream & out) const {
    out << "generic_forall([ ";
    for (Enode * const var : m_forall_vars) {
        out << var << " ";
    }
    out << "], "
        << (m_polarity == l_True ? "" : "!")
        << get_enode() << ")" << endl;
    return out;
}
}  // namespace dreal
