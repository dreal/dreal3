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

#include <algorithm>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/constraint.h"
#include "util/contractor.h"
#include "util/ibex_enode.h"
#include "util/logging.h"

using std::back_inserter;
using std::function;
using std::initializer_list;
using std::unordered_set;
using std::vector;

namespace dreal {

char const * contractor_exception::what() const throw() {
    return "contractor exception";
}

ibex::SystemFactory build_system_factory(box const & box, vector<algebraic_constraint *> const & ctrs) {
    DREAL_LOG_DEBUG << "build_system_factory:";
    ibex::SystemFactory sf;
    unordered_map<string, ibex::Variable const> var_map;  // Needed for translateEnodeToExprCtr
    // Construct System: add Variables
    thread_local static unordered_map<Enode*, ibex::Variable const *> tls_var_cache;
    for (Enode * e : box.get_vars()) {
        string const & name = e->getCar()->getName();
        DREAL_LOG_INFO << "build_system_factory: Add Variable " << name;
        auto var_it = tls_var_cache.find(e);
        ibex::Variable const * var = nullptr;
        if (var_it == tls_var_cache.end()) {
            // Not found
            var = new ibex::Variable(name.c_str());
            tls_var_cache.emplace(e, var);
        } else {
            // Found
            var = var_it->second;
        }
        var_map.emplace(name, *var);
        sf.add_var(*var);
    }
    DREAL_LOG_DEBUG << "build_system_factory: Add Variable: DONE";
    // Construct System: add constraints
    thread_local static unordered_map<Enode *, ibex::ExprCtr const *> tls_exprctr_cache_pos;
    thread_local static unordered_map<Enode *, ibex::ExprCtr const *> tls_exprctr_cache_neg;
    for (algebraic_constraint * ctr : ctrs) {
        DREAL_LOG_INFO << "build_system_factory: Add Constraint: " << *ctr;
        Enode * e = ctr->get_enodes()[0];
        auto p = e->getPolarity();
        assert(p == l_True || p == l_False);
        auto & tls_exprctr_cache = (p == l_True) ? tls_exprctr_cache_pos : tls_exprctr_cache_neg;
        auto exprctr_it = tls_exprctr_cache.find(e);
        ibex::ExprCtr const * exprctr = nullptr;
        if (exprctr_it == tls_exprctr_cache.end()) {
            // Not found
            exprctr = translate_enode_to_exprctr(var_map, e);
            tls_exprctr_cache.emplace(e, exprctr);
        } else {
            // Found
            exprctr = exprctr_it->second;
        }
        DREAL_LOG_INFO << "build_system_factory: Add Constraint: expr: " << *exprctr;
        sf.add_ctr(*exprctr);
    }
    DREAL_LOG_DEBUG << "build_system_factory: Add Constraint: " << "DONE";
    DREAL_LOG_DEBUG << "build_system_factory: DONE";
    return sf;
}

// TODO(soonhok): this is copied from ibex_DefaultSolver.cpp
ibex::System* square_eq_sys(ibex::System& sys) {
    int nb_eq = 0;
    // count the number of equalities
    for (int i = 0; i < sys.nb_ctr; i++) {
        if (sys.ctrs[i].op == ibex::EQ) nb_eq += sys.ctrs[i].f.image_dim();
    }
    if (sys.nb_var == nb_eq) {
        if (nb_eq == sys.f.image_dim()) {
            return &sys;  // useless to create a new one
        } else {
            return new ibex::System(sys, ibex::System::EQ_ONLY);
        }
    } else {
        return nullptr;  // not square
    }
}

ibex::Array<ibex::ExprSymbol const> build_array_of_vars_from_enodes(unordered_set<Enode *> const & s) {
    // TODO(soonhok): the caller has to delete the symbols
    unsigned const size = s.size();
    unsigned i = 0;
    ibex::Array<ibex::ExprSymbol const> ret(size);
    for (auto const e : s) {
        string const & name = e->getCar()->getName();
        ibex::Variable var(name.c_str());
        ret[i++] = (*var.symbol);
    }
    return ret;
}

contractor_ibex_fwdbwd::contractor_ibex_fwdbwd(box const & /* box */, algebraic_constraint const * const ctr)
    : contractor_cell(contractor_kind::IBEX_FWDBWD), m_ctr(ctr) {
    unordered_map<string, ibex::Variable const> var_map;
    m_exprctr = translate_enode_to_exprctr(var_map, ctr->get_enodes()[0]);
    m_var_array.resize(var_map.size());
    unsigned i = 0;
    for (auto const p : var_map) {
        m_var_array.set_ref(i, p.second);
        // TODO(soonhok): m_var_index_map is unnecessary. remove it
        m_var_index_map.emplace(i, p.second.symbol->name);
        i++;
    }
    m_numctr = new ibex::NumConstraint(m_var_array, *m_exprctr);
    m_ctc = new ibex::CtcFwdBwd(*m_numctr);
    m_used_constraints.insert(m_ctr);
}
contractor_ibex_fwdbwd::~contractor_ibex_fwdbwd() {
    delete m_ctc;
    delete m_numctr;
    delete m_exprctr;
}
box contractor_ibex_fwdbwd::prune(box b) const {
    DREAL_LOG_INFO << "==================================================";
    // Construct iv from box b
    ibex::IntervalVector iv(m_var_array.size());
    for (int i = 0; i < m_var_array.size(); i++) {
        iv[i] = b[m_var_index_map.at(i)];
        DREAL_LOG_INFO << m_var_index_map.at(i) << " = " << iv[i];
    }
    // Prune on iv
    try {
        DREAL_LOG_INFO << "Before pruning using ibex_fwdbwd(" << *m_numctr << ")";
        DREAL_LOG_INFO << b;
        DREAL_LOG_INFO << "ibex interval = " << iv << " (before)";
        m_ctc->contract(iv);
    } catch(ibex::EmptyBoxException& e) {
        b.set_empty();
    }
    DREAL_LOG_INFO << "ibex interval = " << iv << " (after)";
    // Reconstruct box b from pruned result iv.
    if (!b.is_empty()) {
        for (int i = 0; i < m_var_array.size(); i++) {
            b[m_var_index_map.at(i)] = iv[i];
        }
    }
    DREAL_LOG_INFO << "After pruning using ibex_fwdbwd(" << *m_numctr << ")";
    DREAL_LOG_INFO << b;
    return b;
}
contractor_ibex::contractor_ibex(box const & box, vector<algebraic_constraint *> const & ctrs)
    : contractor_cell(contractor_kind::IBEX), m_sf(build_system_factory(box, ctrs)), m_sys(m_sf) {
    DREAL_LOG_DEBUG << "contractor_ibex:";
    // TODO(soonhok): parameterize this one.
    double const prec = 0.001;
    unsigned index = 0;

    ibex::Array<ibex::Ctc> ctc_list(4);
    ibex::CtcHC4 * ctc_hc4 = new ibex::CtcHC4(m_sys.ctrs, 0.01);
    ctc_list.set_ref(index++, *ctc_hc4);
    m_sub_ctcs.push_back(ctc_hc4);

    ibex::CtcAcid * ctc_acid = new ibex::CtcAcid(m_sys, *ctc_hc4);
    ctc_list.set_ref(index++, *ctc_acid);
    m_sub_ctcs.push_back(ctc_acid);

    m_sys_eqs = square_eq_sys(m_sys);
    if (m_sys_eqs) {
        DREAL_LOG_INFO << "contractor_ibex: SQUARE SYSTEM";
        ibex::CtcNewton * ctc_newton = new ibex::CtcNewton(m_sys_eqs->f, 5e8, prec, 1.e-4);
        ctc_list.set_ref(index++, *ctc_newton);
        m_sub_ctcs.push_back(ctc_newton);
    }

    m_lrc = new ibex::LinearRelaxCombo(m_sys, ibex::LinearRelaxCombo::XNEWTON);
    ibex::CtcPolytopeHull * ctc_ph = new ibex::CtcPolytopeHull(*m_lrc, ibex::CtcPolytopeHull::ALL_BOX);
    ibex::CtcCompo * ctc_combo = new ibex::CtcCompo(*ctc_ph, *ctc_hc4);
    m_sub_ctcs.push_back(ctc_ph);
    m_sub_ctcs.push_back(ctc_combo);
    ibex::CtcFixPoint * ctc_fp = new ibex::CtcFixPoint(*ctc_combo);
    m_sub_ctcs.push_back(ctc_fp);
    ctc_list.set_ref(index++, *ctc_fp);

    ctc_list.resize(index);
    m_ctc = new ibex::CtcCompo (ctc_list);
    DREAL_LOG_DEBUG << "contractor_ibex: DONE";
}

contractor_ibex::~contractor_ibex() {
    DREAL_LOG_DEBUG << "~contractor_ibex: DELETED";
    delete m_lrc;
    for (ibex::Ctc * sub_ctc : m_sub_ctcs) {
        delete sub_ctc;
    }
    delete m_ctc;
    delete m_sys_eqs;
}

box contractor_ibex::prune(box b) const {
    try {
        m_ctc->contract(b.get_values());
    } catch(ibex::EmptyBoxException&) {
        assert(b.is_empty());
    }
    return b;
}

contractor_seq::contractor_seq(initializer_list<contractor> const & l)
    : contractor_cell(contractor_kind::SEQ), m_vec(l) { }
box contractor_seq::prune(box b) const {
    for (contractor const & c : m_vec) {
        b = c.prune(b);
        unordered_set<constraint const *> const & used_ctrs = c.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        if (b.is_empty()) {
            return b;
        }
    }
    return b;
}

contractor_try::contractor_try(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::TRY), m_c1(c1), m_c2(c2) { }
box contractor_try::prune(box b) const {
    try {
        b = m_c1.prune(b);
        unordered_set<constraint const *> const & used_ctrs = m_c1.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    } catch (contractor_exception & e) {
        b = m_c2.prune(b);
        unordered_set<constraint const *> const & used_ctrs = m_c2.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    }
}

contractor_ite::contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else)
    : contractor_cell(contractor_kind::ITE), m_guard(guard), m_c_then(c_then), m_c_else(c_else) { }
box contractor_ite::prune(box b) const {
    if (m_guard(b)) {
        b = m_c_then.prune(b);
        unordered_set<constraint const *> const & used_ctrs = m_c_then.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    } else {
        b = m_c_else.prune(b);
        unordered_set<constraint const *> const & used_ctrs = m_c_else.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    }
}

contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> guard, contractor const & c)
    : contractor_cell(contractor_kind::FP), m_guard(guard), m_clist(1, c) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> guard, initializer_list<contractor> const & clist)
    : contractor_cell(contractor_kind::FP), m_guard(guard), m_clist(clist) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> guard, vector<contractor> const & cvec)
    : contractor_cell(contractor_kind::FP), m_guard(guard), m_clist(cvec) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> guard,
                                         vector<contractor> const & cvec1, vector<contractor> const & cvec2)
    : contractor_cell(contractor_kind::FP), m_guard(guard), m_clist(cvec1) {
    copy(cvec2.begin(), cvec2.end(), back_inserter(m_clist));
}

box contractor_fixpoint::prune(box old_b) const {
    box new_b = old_b;
    do {
        old_b = new_b;
        for (contractor const & c : m_clist) {
            // DREAL_LOG_INFO << new_b;
            new_b = c.prune(new_b);
            unordered_set<constraint const *> const & used_constraints = c.used_constraints();
            m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
            if (new_b.is_empty()) {
                return new_b;
            }
        }
    } while (m_guard(old_b, new_b));
    return new_b;
}

// TODO(soonhok): need to take alg/ode constraints
contractor_int::contractor_int() : contractor_cell(contractor_kind::INT) { }
box contractor_int::prune(box b) const {
    unsigned i = 0;
    ibex::IntervalVector iv = b.get_values();
    for (Enode * e : b.get_vars()) {
        if (e->hasSortInt()) {
            iv[i] = ibex::integer(iv[i]);
        }
        i++;
        // TODO(soonhok): stop when iv[i] is empty
    }
    return b;
}

contractor mk_contractor_ibex(box const & box, vector<algebraic_constraint *> const & ctrs) {
    return contractor(shared_ptr<contractor_cell>(new contractor_ibex(box, ctrs)));
}

contractor mk_contractor_ibex_fwdbwd(box const & box, algebraic_constraint const * const ctr) {
    return contractor(shared_ptr<contractor_cell>(new contractor_ibex_fwdbwd(box, ctr)));
}
contractor mk_contractor_seq(initializer_list<contractor> const & l) {
    return contractor(shared_ptr<contractor_cell>(new contractor_seq(l)));
}
contractor mk_contractor_try(contractor const & c1, contractor const & c2) {
    return contractor(shared_ptr<contractor_cell>(new contractor_try(c1, c2)));
}
contractor mk_contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else) {
    return contractor(shared_ptr<contractor_cell>(new contractor_ite(guard, c_then, c_else)));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, contractor const & c) {
    return contractor(shared_ptr<contractor_cell>(new contractor_fixpoint(guard, c)));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, initializer_list<contractor> const & clist) {
    return contractor(shared_ptr<contractor_cell>(new contractor_fixpoint(guard, clist)));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, vector<contractor> const & cvec) {
    return contractor(shared_ptr<contractor_cell>(new contractor_fixpoint(guard, cvec)));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard,
                                  vector<contractor> const & cvec1, vector<contractor> const & cvec2) {
    return contractor(shared_ptr<contractor_cell>(new contractor_fixpoint(guard, cvec1, cvec2)));
}
contractor mk_contractor_int() {
    return contractor(shared_ptr<contractor_cell>(new contractor_int()));
}
}  // namespace dreal
