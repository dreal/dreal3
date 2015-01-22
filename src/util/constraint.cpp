/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

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

#include <vector>
#include <string>
#include <algorithm>
#include <iterator>
#include <unordered_map>
#include <initializer_list>
#include <iostream>
#include "opensmt/egraph/Enode.h"
#include "util/constraint.h"
#include "util/flow.h"

using std::back_inserter;
using std::copy;
using std::endl;
using std::initializer_list;
using std::ostream;
using std::string;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::to_string;

namespace dreal {

ostream & operator<<(ostream & out, constraint_type const & ty) {
    switch (ty) {
    case constraint_type::Algebraic:
        out << "Algebraic";
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
    default:
        throw std::logic_error("unmatched case in ostream & operator<<(ostream & out, constraint_type const & ty)");
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
    copy(enodes_2.begin(), enodes_2.end(), back_inserter(m_enodes));
}
ostream & operator<<(ostream & out, constraint const & c) {
    return c.display(out);
}

// ====================================================
// Algebraic constraint
// ====================================================
algebraic_constraint::algebraic_constraint(Enode * const e)
    : constraint(constraint_type::Algebraic, e) {
}
algebraic_constraint::~algebraic_constraint() { }
ostream & algebraic_constraint::display(ostream & out) const {
    out << "algebraic_constraint " << m_enodes[0];
    return out;
}

// ====================================================
// Algebraic constraint
// ====================================================
ode_constraint::ode_constraint(integral_constraint const & integral, vector<forallt_constraint> const & invs)
    : constraint(constraint_type::ODE, integral.get_enodes()), m_int(integral), m_invs(invs) {
    for (auto const & inv : invs) {
        copy(inv.get_enodes().begin(), inv.get_enodes().end(), back_inserter(m_enodes));
    }
}
ode_constraint::~ode_constraint() {
    // TODO(soonhok): implement this?
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

    vector<Enode *> vars_0, vars_t;
    while (!tmp->isEnil()) {
        vars_0.push_back(tmp->getCar());
        tmp = tmp->getCdr();
        vars_t.push_back(tmp->getCar());
        tmp = tmp->getCdr();
    }
    string key = string("flow_") + to_string(flow_id);
    auto const it = flow_map.find(key);
    if (it != flow_map.end()) {
        flow const & _flow = it->second;
        return integral_constraint(e, flow_id, time_0, time_t, vars_0, vars_t, _flow);
    } else {
        throw std::logic_error(key + " is not in flow_map. Failed to create integral constraint");
    }
}
integral_constraint::integral_constraint(Enode * const e, unsigned const flow_id, Enode * const time_0, Enode * const time_t,
                                         vector<Enode *> const & vars_0, vector<Enode *> const & vars_t,
                                         flow const & _flow)
    : constraint(constraint_type::Integral, e),
      m_flow_id(flow_id), m_time_0(time_0), m_time_t(time_t), m_vars_0(vars_0), m_vars_t(vars_t), m_flow(_flow) { }
integral_constraint::~integral_constraint() {
}
ostream & integral_constraint::display(ostream & out) const {
    out << "integral_constraint = " << m_enodes[0] << endl;
    out << "\t" << "flow_id = " << m_flow_id << endl;
    out << "\t" << "time = [" << m_time_0 << "," << m_time_t << "]" << endl;
    for (Enode * var_0 : m_vars_0) {
        out << "\t" << "var_0 : " << var_0 << endl;
    }
    for (Enode * var_t : m_vars_t) {
        out << "\t" << "var_t : " << var_t << endl;
    }
    out << m_flow << endl;
    return out;
}


forallt_constraint mk_forallt_constraint(Enode * const e) {
    // nra_solver::inform: (forallt 2 0 time_9 (<= 0 v_9_t))
    Enode const * tmp = e->getCdr();
    unsigned const flow_id = tmp->getCar()->getValue();
    tmp = tmp->getCdr();

    Enode * const time_0 = tmp->getCar();
    tmp = tmp->getCdr();

    Enode * const time_t = tmp->getCar();
    tmp = tmp->getCdr();

    Enode * const inv = tmp->getCar();
    return forallt_constraint(e, flow_id, time_0, time_t, inv);
}

// ====================================================
// ForallT constraint
// ====================================================
forallt_constraint::forallt_constraint(Enode * const e, unsigned const flow_id, Enode * const time_0, Enode * const time_t, Enode * const inv)
    : constraint(constraint_type::ForallT, e), m_flow_id(flow_id), m_time_0(time_0), m_time_t(time_t), m_inv(inv) {
}
forallt_constraint::~forallt_constraint() {
}
ostream & forallt_constraint::display(ostream & out) const {
    out << "forallt_constraint = " << m_enodes[0] << endl;
    out << "\t" << "flow_id = " << m_flow_id << endl;
    out << "\t" << "time = [" << m_time_0 << "," << m_time_t << "]" << endl;
    out << "\t" << "inv : " << m_inv << endl;
    return out;
}
}  // namespace dreal
