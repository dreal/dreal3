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
#include <map>
#include <memory>
#include <queue>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "contractor/contractor.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/constraint.h"
#include "util/ibex_enode.h"
#include "util/logging.h"
#include "util/proof.h"

using std::make_shared;
using std::back_inserter;
using std::function;
using std::initializer_list;
using std::unordered_set;
using std::vector;
using std::queue;

namespace dreal {
ibex::SystemFactory* build_system_factory(box const & box, vector<nonlinear_constraint const *> const & ctrs) {
    DREAL_LOG_DEBUG << "build_system_factory:";
    ibex::SystemFactory * sf = new ibex::SystemFactory();
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
        sf->add_var(*var);
    }
    DREAL_LOG_DEBUG << "build_system_factory: Add Variable: DONE";
    // Construct System: add constraints
    thread_local static unordered_map<Enode *, ibex::ExprCtr const *> tls_exprctr_cache_pos;
    thread_local static unordered_map<Enode *, ibex::ExprCtr const *> tls_exprctr_cache_neg;
    for (nonlinear_constraint const * ctr : ctrs) {
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
            sf->add_ctr(*exprctr);
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

contractor_ibex_fwdbwd::contractor_ibex_fwdbwd(box const & box, nonlinear_constraint const * const ctr)
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
    delete m_ctc;
}
box contractor_ibex_fwdbwd::prune(box b, SMTConfig & config) const {
    if (m_ctc == nullptr) { return b; }

    // ======= Proof =======
    thread_local static box old_box(b);
    if (config.nra_proof) { old_box = b; }

    DREAL_LOG_DEBUG << "==================================================";
    // Construct iv from box b
    ibex::IntervalVector iv(m_var_array.size());
    for (int i = 0; i < m_var_array.size(); i++) {
        iv[i] = b[m_var_array[i].name];
        DREAL_LOG_DEBUG << m_var_array[i].name << " = " << iv[i];
    }
    // Prune on iv
    DREAL_LOG_DEBUG << "Before pruning using ibex_fwdbwd(" << *m_numctr << ")";
    DREAL_LOG_DEBUG << b;
    DREAL_LOG_DEBUG << "ibex interval = " << iv << " (before)";
    DREAL_LOG_DEBUG << "function = " << m_ctc->f;
    DREAL_LOG_DEBUG << "domain   = " << m_ctc->d;
    m_ctc->contract(iv);
    DREAL_LOG_DEBUG << "ibex interval = " << iv << " (after)";
    if (iv.is_empty()) {
        b.set_empty();
    } else {
        // Reconstruct box b from pruned result iv.
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

    // ======= Proof =======
    if (config.nra_proof) {
        stringstream ss;
        Enode const * const e = m_ctr->get_enodes()[0];
        ss << (e->getPolarity() == l_False ? "!" : "") << e;
        output_pruning_step(config.nra_proof_out, old_box, b, config.nra_readable_proof, ss.str());
    }
    return b;
}
ostream & contractor_ibex_fwdbwd::display(ostream & out) const {
    out << "contractor_ibex_fwdbwd(";
    if (m_ctc != nullptr) {
        out << *m_numctr;
    }
    out << ")";
    return out;
}

void contractor_ibex_polytope::init(box const & box) const {
    m_sf = build_system_factory(box, m_ctrs);
    m_sys = new ibex::System(*m_sf);

    unsigned index = 0;

    ibex::Array<ibex::Ctc> ctc_list(2);

    m_sys_eqs = square_eq_sys(*m_sys);
    if (m_sys_eqs) {
        DREAL_LOG_INFO << "contractor_ibex_polytope: SQUARE SYSTEM";
        ibex::CtcNewton * ctc_newton = new ibex::CtcNewton(m_sys_eqs->f, 5e8, m_prec, 1.e-4);
        ctc_list.set_ref(index++, *ctc_newton);
        m_sub_ctcs.push_back(ctc_newton);
    }

    m_lrc = new ibex::LinearRelaxCombo(*m_sys, ibex::LinearRelaxCombo::XNEWTON);
    ibex::CtcPolytopeHull * ctc_ph = new ibex::CtcPolytopeHull(*m_lrc, ibex::CtcPolytopeHull::ALL_BOX);
    ibex::CtcHC4 * ctc_hc4 = new ibex::CtcHC4(m_sys->ctrs, m_prec);
    ibex::CtcCompo * ctc_combo = new ibex::CtcCompo(*ctc_ph, *ctc_hc4);
    m_sub_ctcs.push_back(ctc_ph);
    m_sub_ctcs.push_back(ctc_hc4);
    m_sub_ctcs.push_back(ctc_combo);
    ibex::CtcFixPoint * ctc_fp = new ibex::CtcFixPoint(*ctc_combo);
    m_sub_ctcs.push_back(ctc_fp);
    ctc_list.set_ref(index++, *ctc_fp);

    ctc_list.resize(index);
    m_ctc = new ibex::CtcCompo (ctc_list);

    // Setup Input
    // TODO(soonhok): this is a rough approximation, which needs to be refined.
    m_input  = ibex::BitSet::all(box.size());
    m_used_constraints.insert(m_ctrs.begin(), m_ctrs.end());
    DREAL_LOG_DEBUG << "contractor_ibex_polytope: DONE";
}

contractor_ibex_polytope::contractor_ibex_polytope(double const prec, vector<nonlinear_constraint const *> const & ctrs)
    : contractor_cell(contractor_kind::IBEX_POLYTOPE), m_ctrs(ctrs), m_prec(prec) {
}

contractor_ibex_polytope::~contractor_ibex_polytope() {
    DREAL_LOG_DEBUG << "~contractor_ibex_polytope: DELETED";
    delete m_lrc;
    for (ibex::Ctc * sub_ctc : m_sub_ctcs) {
        delete sub_ctc;
    }
    delete m_ctc;
    if (m_sys_eqs && m_sys_eqs != m_sys) { delete m_sys_eqs; }
    delete m_sys;
    delete m_sf;
}

box contractor_ibex_polytope::prune(box b, SMTConfig & config) const {
    if (!m_ctc) { init(b); }
    thread_local static box old_box(b);
    old_box = b;
    m_ctc->contract(b.get_values());
    // setup output
    vector<bool> diff_dims = b.diff_dims(old_box);
    m_output = ibex::BitSet::empty(old_box.size());
    for (unsigned i = 0; i < diff_dims.size(); i++) {
        if (diff_dims[i]) {
            m_output.add(i);
        }
    }
    // ======= Proof =======
    if (config.nra_proof) {
        stringstream ss;
        for (auto const & ctr : m_ctrs) {
            Enode const * const e = ctr->get_enodes()[0];
            ss << (e->getPolarity() == l_False ? "!" : "") << e << ";";
        }
        output_pruning_step(config.nra_proof_out, old_box, b, config.nra_readable_proof, ss.str());
    }
    return b;
}
ostream & contractor_ibex_polytope::display(ostream & out) const {
    out << "contractor_ibex_polytope(";
    for (unsigned i = 0; i < m_ctrs.size(); i++) {
        out << *m_ctrs[i] << ", ";
    }
    out << ")";
    return out;
}

contractor mk_contractor_ibex_polytope(double const prec, vector<nonlinear_constraint const *> const & ctrs) {
    return contractor(make_shared<contractor_ibex_polytope>(prec, ctrs));
}

contractor mk_contractor_ibex_fwdbwd(box const & box, nonlinear_constraint const * const ctr) {
    static thread_local unordered_map<nonlinear_constraint const *, contractor> cache;
    auto const it = cache.find(ctr);
    if (it == cache.cend()) {
        contractor ctc(make_shared<contractor_ibex_fwdbwd>(box, ctr));
        cache.emplace(ctr, ctc);
        return ctc;
    } else {
        return it->second;
    }
}
}  // namespace dreal
