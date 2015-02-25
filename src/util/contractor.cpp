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
#include <queue>
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/constraint.h"
#include "util/contractor.h"
#include "util/ibex_enode.h"
#include "util/logging.h"

using std::make_shared;
using std::back_inserter;
using std::function;
using std::initializer_list;
using std::unordered_set;
using std::vector;
using std::queue;

namespace dreal {

char const * contractor_exception::what() const throw() {
    return "contractor exception";
}

std::ostream & operator<<(std::ostream & out, contractor_cell const & c) {
    return c.display(out);
}
ibex::SystemFactory build_system_factory(box const & box, vector<algebraic_constraint const *> const & ctrs) {
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
    for (algebraic_constraint const * ctr : ctrs) {
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
        if (exprctr) {
            DREAL_LOG_INFO << "build_system_factory: Add Constraint: expr: " << *exprctr;
            sf.add_ctr(*exprctr);
        }
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

contractor_ibex_fwdbwd::contractor_ibex_fwdbwd(box const & box, algebraic_constraint const * const ctr)
    : contractor_cell(contractor_kind::IBEX_FWDBWD, box.size()), m_ctr(ctr),
      m_numctr(ctr->get_numctr()), m_var_array(ctr->get_var_array()) {
    if (m_numctr) {
        m_ctc = new ibex::CtcFwdBwd(*m_numctr);
        // Set up input
        ibex::BitSet const * const input = m_ctc->input;
        for (unsigned i = 0; i <  input->size(); i++) {
            if ((*input)[i]) {
                m_input.add(box.get_index(m_var_array[i].name));
            }
        }
        m_used_constraints.insert(m_ctr);
    }
}
contractor_ibex_fwdbwd::~contractor_ibex_fwdbwd() {
    if (m_ctc) { delete m_ctc; }
}
box contractor_ibex_fwdbwd::prune(box b) const {
    if (m_ctc == nullptr) {
        return b;
    }
    DREAL_LOG_DEBUG << "==================================================";
    // Construct iv from box b
    ibex::IntervalVector iv(m_var_array.size());
    for (int i = 0; i < m_var_array.size(); i++) {
        iv[i] = b[m_var_array[i].name];
        DREAL_LOG_DEBUG << m_var_array[i].name << " = " << iv[i];
    }
    // Prune on iv
    try {
        DREAL_LOG_DEBUG << "Before pruning using ibex_fwdbwd(" << *m_numctr << ")";
        DREAL_LOG_DEBUG << b;
        DREAL_LOG_DEBUG << "ibex interval = " << iv << " (before)";
        DREAL_LOG_DEBUG << "function = " << m_ctc->f;
        DREAL_LOG_DEBUG << "domain   = " << m_ctc->d;
        m_ctc->contract(iv);
    } catch(ibex::EmptyBoxException& e) {
        b.set_empty();
    }
    DREAL_LOG_DEBUG << "ibex interval = " << iv << " (after)";
    // Reconstruct box b from pruned result iv.
    if (!b.is_empty()) {
        for (int i = 0; i < m_var_array.size(); i++) {
            b[m_var_array[i].name] = iv[i];
        }
    }
    ibex::BitSet const * const output = m_ctc->output;
    for (unsigned i = 0; i <  output->size(); i++) {
        if ((*output)[i]) {
            m_output.add(b.get_index(m_var_array[i].name));
        }
    }

    DREAL_LOG_DEBUG << "After pruning using ibex_fwdbwd(" << *m_numctr << ")";
    DREAL_LOG_DEBUG << b;
    return b;
}
ostream & contractor_ibex_fwdbwd::display(ostream & out) const {
    if (m_ctc != nullptr) {
        out << "contractor_ibex_fwdbwd(" << *m_numctr << ")";
    }
    return out;
}
contractor_ibex::contractor_ibex(double const prec, box const & box, vector<algebraic_constraint const *> const & ctrs)
    : contractor_cell(contractor_kind::IBEX), m_prec(prec), m_sf(build_system_factory(box, ctrs)), m_sys(m_sf) {
    DREAL_LOG_DEBUG << "contractor_ibex:";
    unsigned index = 0;

    ibex::Array<ibex::Ctc> ctc_list(4);
    ibex::CtcHC4 * ctc_hc4 = new ibex::CtcHC4(m_sys.ctrs, m_prec);
    ctc_list.set_ref(index++, *ctc_hc4);
    m_sub_ctcs.push_back(ctc_hc4);

    ibex::CtcAcid * ctc_acid = new ibex::CtcAcid(m_sys, *ctc_hc4);
    ctc_list.set_ref(index++, *ctc_acid);
    m_sub_ctcs.push_back(ctc_acid);

    m_sys_eqs = square_eq_sys(m_sys);
    if (m_sys_eqs) {
        DREAL_LOG_INFO << "contractor_ibex: SQUARE SYSTEM";
        ibex::CtcNewton * ctc_newton = new ibex::CtcNewton(m_sys_eqs->f, 5e8, m_prec, 1.e-4);
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

    // Setup Input
    // TODO(soonhok): this is a rough approximation, which needs to be refined.
    m_input  = ibex::BitSet::all(box.size());
    m_used_constraints.insert(ctrs.begin(), ctrs.end());
    DREAL_LOG_DEBUG << "contractor_ibex: DONE";
}

contractor_ibex::~contractor_ibex() {
    DREAL_LOG_DEBUG << "~contractor_ibex: DELETED";
    delete m_lrc;
    for (ibex::Ctc * sub_ctc : m_sub_ctcs) {
        delete sub_ctc;
    }
    delete m_ctc;
    if (m_sys_eqs && m_sys_eqs != &m_sys) {
        delete m_sys_eqs;
    }
}

box contractor_ibex::prune(box b) const {
    box old_box = b;
    try {
        m_ctc->contract(b.get_values());
    } catch(ibex::EmptyBoxException&) {
        assert(b.is_empty());
    }
    // setup output
    vector<bool> diff_dims = b.diff_dims(old_box);
    m_output = ibex::BitSet::empty(old_box.size());
    for (unsigned i = 0; i < diff_dims.size(); i++) {
        if (diff_dims[i]) {
            m_output.add(i);
        }
    }
    return b;
}
ostream & contractor_ibex::display(ostream & out) const {
    out << "contractor_ibex(";
    for (int i = 0; i < m_numctrs.size(); i++) {
        out << m_numctrs[i] << ", ";
    }
    out << ")";
    return out;
}

contractor_seq::contractor_seq(initializer_list<contractor> const & l)
    : contractor_cell(contractor_kind::SEQ), m_vec(l) { }
box contractor_seq::prune(box b) const {
    m_input  = ibex::BitSet::empty(b.size());
    m_output = ibex::BitSet::empty(b.size());
    for (contractor const & c : m_vec) {
        b = c.prune(b);
        m_input.union_with(c.input());
        m_output.union_with(c.output());
        unordered_set<constraint const *> const & used_ctrs = c.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        if (b.is_empty()) {
            return b;
        }
    }
    return b;
}
ostream & contractor_seq::display(ostream & out) const {
    out << "contractor_seq(";
    for (contractor const & c : m_vec) {
        out << c << ", ";
    }
    out << ")";
    return out;
}

contractor_try::contractor_try(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::TRY), m_c1(c1), m_c2(c2) { }
box contractor_try::prune(box b) const {
    try {
        b = m_c1.prune(b);
        m_input  = m_c1.input();
        m_output = m_c1.input();
        unordered_set<constraint const *> const & used_ctrs = m_c1.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    } catch (contractor_exception & e) {
        b = m_c2.prune(b);
        m_input  = m_c2.input();
        m_output = m_c2.input();
        unordered_set<constraint const *> const & used_ctrs = m_c2.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    }
}
ostream & contractor_try::display(ostream & out) const {
    out << "contractor_try("
        << m_c1 << ", "
        << m_c2 << ")";
    return out;
}

contractor_ite::contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else)
    : contractor_cell(contractor_kind::ITE), m_guard(guard), m_c_then(c_then), m_c_else(c_else) { }
box contractor_ite::prune(box b) const {
    if (m_guard(b)) {
        b = m_c_then.prune(b);
        m_input  = m_c_then.input();
        m_output = m_c_then.input();
        unordered_set<constraint const *> const & used_ctrs = m_c_then.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    } else {
        b = m_c_else.prune(b);
        m_input  = m_c_else.input();
        m_output = m_c_else.input();
        unordered_set<constraint const *> const & used_ctrs = m_c_else.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        return b;
    }
}
ostream & contractor_ite::display(ostream & out) const {
    out << "contractor_ite("
        << m_c_then << ", "
        << m_c_else << ")";
    return out;
}

contractor_fixpoint::contractor_fixpoint(double const p, function<bool(box const &, box const &)> term_cond, contractor const & c)
    : contractor_cell(contractor_kind::FP), m_prec(p), m_term_cond(term_cond), m_clist(1, c) { }
contractor_fixpoint::contractor_fixpoint(double const p, function<bool(box const &, box const &)> term_cond, initializer_list<contractor> const & clist)
    : contractor_cell(contractor_kind::FP), m_prec(p), m_term_cond(term_cond), m_clist(clist) { }
contractor_fixpoint::contractor_fixpoint(double const p, function<bool(box const &, box const &)> term_cond, vector<contractor> const & cvec)
    : contractor_cell(contractor_kind::FP), m_prec(p), m_term_cond(term_cond), m_clist(cvec) { }
contractor_fixpoint::contractor_fixpoint(double const p, function<bool(box const &, box const &)> term_cond,
                                         vector<contractor> const & cvec1, vector<contractor> const & cvec2)
    : contractor_cell(contractor_kind::FP), m_prec(p), m_term_cond(term_cond), m_clist(cvec1) {
    copy(cvec2.begin(), cvec2.end(), back_inserter(m_clist));
}

box contractor_fixpoint::prune(box old_b) const {
//    box naive_result const & = naive_fixpoint_alg(old_b);
//    return naive_result;
    box const & worklist_result = worklist_fixpoint_alg(old_b);
    return worklist_result;
}
ostream & contractor_fixpoint::display(ostream & out) const {
    out << "contractor_fixpoint(";
    for (contractor const & c : m_clist) {
        out << c << ", " << endl;
    }
    out << ")";
    return out;
}

box contractor_fixpoint::naive_fixpoint_alg(box old_box) const {
    box new_box = old_box;
    m_input  = ibex::BitSet::empty(old_box.size());
    m_output = ibex::BitSet::empty(old_box.size());
    // Fixed Point Loop
    do {
        old_box = new_box;
        for (contractor const & c : m_clist) {
            new_box = c.prune(new_box);
            m_input.union_with(c.input());
            m_output.union_with(c.output());
            unordered_set<constraint const *> const & used_constraints = c.used_constraints();
            m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
            if (new_box.is_empty()) {
                return new_box;
            }
        }
    } while (!m_term_cond(old_box, new_box));
    return new_box;
}

box contractor_fixpoint::worklist_fixpoint_alg(box old_box) const {
    box new_box = old_box;
    m_input  = ibex::BitSet::empty(old_box.size());
    m_output = ibex::BitSet::empty(old_box.size());

    // Add all contractors to the queue.
    unordered_set<contractor> c_set;
    queue<contractor> q;

    for (contractor const & c : m_clist) {
        if (c_set.find(c) == c_set.end()) {
            q.push(c);
            c_set.insert(c);
        }
    }
    unsigned const num_initial_ctcs = c_set.size();
    unsigned count = 0;
    // Fixed Point Loop
    do {
        old_box = new_box;
        contractor const & c = q.front();
        new_box = c.prune(new_box);
        count++;
        m_input.union_with(c.input());
        m_output.union_with(c.output());
        unordered_set<constraint const *> const & used_constraints = c.used_constraints();
        m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
        if (new_box.is_empty()) {
            return new_box;
        }
        c_set.erase(c);
        q.pop();

        vector<bool> diff_dims = new_box.diff_dims(old_box);
        for (unsigned i = 0; i < diff_dims.size(); i++) {
            if (diff_dims[i]) {
                for (contractor const & c : m_clist) {
                    if (c.input()[i]) {
                        if (c_set.find(c) == c_set.end()) {
                            q.push(c);
                            c_set.insert(c);
                        }
                        break;
                    }
                }
            }
        }
    } while ((count < num_initial_ctcs) || !m_term_cond(old_box, new_box));
    return new_box;
}

contractor_int::contractor_int() : contractor_cell(contractor_kind::INT) { }
box contractor_int::prune(box b) const {
    m_input  = ibex::BitSet::empty(b.size());
    m_output = ibex::BitSet::empty(b.size());
    unsigned i = 0;
    ibex::IntervalVector iv = b.get_values();
    for (Enode * e : b.get_vars()) {
        if (e->hasSortInt()) {
            auto old_iv = iv[i];
            iv[i] = ibex::integer(iv[i]);
            if (old_iv != iv[i]) {
                m_input.add(i);
                m_output.add(i);
            }
            if (iv[i].is_empty()) {
                b.set_empty();
                break;
            }
        }
        i++;
    }
    return b;
}
ostream & contractor_int::display(ostream & out) const {
    out << "contractor_int()";
    return out;
}

contractor mk_contractor_ibex(double const prec, box const & box, vector<algebraic_constraint const *> const & ctrs) {
    return contractor(make_shared<contractor_ibex>(prec, box, ctrs));
}

contractor mk_contractor_ibex_fwdbwd(box const & box, algebraic_constraint const * const ctr) {
    static thread_local unordered_map<algebraic_constraint const *, contractor> cache;
    auto const it = cache.find(ctr);
    if (it == cache.cend()) {
        contractor ctc(make_shared<contractor_ibex_fwdbwd>(box, ctr));
        cache.emplace(ctr, ctc);
        return ctc;
    } else {
        return it->second;
    }
}
contractor mk_contractor_seq(initializer_list<contractor> const & l) {
    return contractor(make_shared<contractor_seq>(l));
}
contractor mk_contractor_try(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_try>(c1, c2));
}
contractor mk_contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else) {
    return contractor(make_shared<contractor_ite>(guard, c_then, c_else));
}
contractor mk_contractor_fixpoint(double const p, function<bool(box const &, box const &)> guard, contractor const & c) {
    return contractor(make_shared<contractor_fixpoint>(p, guard, c));
}
contractor mk_contractor_fixpoint(double const p, function<bool(box const &, box const &)> guard, initializer_list<contractor> const & clist) {
    return contractor(make_shared<contractor_fixpoint>(p, guard, clist));
}
contractor mk_contractor_fixpoint(double const p, function<bool(box const &, box const &)> guard, vector<contractor> const & cvec) {
    return contractor(make_shared<contractor_fixpoint>(p, guard, cvec));
}
contractor mk_contractor_fixpoint(double const p, function<bool(box const &, box const &)> guard,
                                  vector<contractor> const & cvec1, vector<contractor> const & cvec2) {
    return contractor(make_shared<contractor_fixpoint>(p, guard, cvec1, cvec2));
}
contractor mk_contractor_int() {
    return contractor(make_shared<contractor_int>());
}

std::ostream & operator<<(std::ostream & out, contractor const & c) {
    out << *(c.m_ptr);
    return out;
}

}  // namespace dreal
