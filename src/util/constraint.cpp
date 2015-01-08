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
#include <algorithm>
#include <iterator>
#include <unordered_map>
#include <initializer_list>
#include "opensmt/egraph/Enode.h"
#include "util/constraint.h"

using std::back_inserter;
using std::copy;
using std::endl;
using std::initializer_list;
using std::ostream;
using std::unordered_set;
using std::vector;

namespace dreal {

// ====================================================
// constraint
// ====================================================
constraint::constraint(constraint_type ty) : m_type(ty) {
}
constraint::constraint(constraint_type ty, Enode * e)
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

constraint::constraint(constraint_type ty, std::vector<Enode *> const & enodes)
    : m_type(ty), m_enodes(enodes), m_vars(build_vars_from_enodes({enodes})) {
}
constraint::constraint(constraint_type ty, std::vector<Enode *> const & enodes_1, std::vector<Enode *> const & enodes_2)
    : m_type(ty), m_enodes(enodes_1), m_vars(build_vars_from_enodes({enodes_1, enodes_2})) {
    copy(enodes_2.begin(), enodes_2.end(), back_inserter(m_enodes));
}
ostream & operator<<(ostream & out, constraint const & c) {
    return c.display(out);
}

// ====================================================
// Algebraic constraint
// ====================================================
algebraic_constraint::algebraic_constraint(Enode * e)
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
integral_constraint::integral_constraint(Enode * e)
    : constraint(constraint_type::Integral, e) {
    // nra_solver::inform: (integral 2 0 time_9 v_9_0 v_9_t x_9_0 x_9_t)
    e = e->getCdr();
    m_flow = e->getCar()->getValue();
    e = e->getCdr();

    m_time_0 = e->getCar();
    e = e->getCdr();

    m_time_t = e->getCar();
    e = e->getCdr();

    while (!e->isEnil()) {
        m_vars_0.push_back(e->getCar());
        e = e->getCdr();
        m_vars_t.push_back(e->getCar());
        e = e->getCdr();
    }
}
integral_constraint::~integral_constraint() {
}
ostream & integral_constraint::display(ostream & out) const {
    out << "integral_constraint = " << m_enodes[0] << endl;
    out << "\t" << "flow = " << m_flow << endl;
    out << "\t" << "time = [" << m_time_0 << "," << m_time_t << "]" << endl;
    for (Enode * var_0 : m_vars_0) {
        out << "\t" << "var_0 : " << var_0 << endl;
    }
    for (Enode * var_t : m_vars_t) {
        out << "\t" << "var_t : " << var_t << endl;
    }
    return out;
}

// ====================================================
// ForallT constraint
// ====================================================
forallt_constraint::forallt_constraint(Enode * e)
    : constraint(constraint_type::ForallT, e) {
    // nra_solver::inform: (forallt 2 0 time_9 (<= 0 v_9_t))
    e = e->getCdr();
    m_flow = e->getCar()->getValue();
    e = e->getCdr();

    m_time_0 = e->getCar();
    e = e->getCdr();

    m_time_t = e->getCar();
    e = e->getCdr();

    m_inv = e->getCar();
}
forallt_constraint::~forallt_constraint() {
}
ostream & forallt_constraint::display(ostream & out) const {
    out << "forallt_constraint = " << m_enodes[0] << endl;
    out << "\t" << "flow = " << m_flow << endl;
    out << "\t" << "time = [" << m_time_0 << "," << m_time_t << "]" << endl;
    out << "\t" << "inv : " << m_inv << endl;
    return out;
}
}
