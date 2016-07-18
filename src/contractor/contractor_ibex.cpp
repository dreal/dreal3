/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, the dReal Team

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
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "contractor/contractor_ibex.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "util/ibex_enode.h"
#include "util/logging.h"
#include "util/proof.h"

using std::back_inserter;
using std::cerr;
using std::endl;
using std::function;
using std::initializer_list;
using std::make_pair;
using std::make_shared;
using std::map;
using std::move;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::queue;
using std::shared_ptr;
using std::string;
using std::tuple;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {
ibex::SystemFactory* contractor_ibex_polytope::build_system_factory(vector<Enode *> const & vars, vector<shared_ptr<nonlinear_constraint>> const & ctrs) {
    DREAL_LOG_DEBUG << "build_system_factory:";
    ibex::SystemFactory * sf = new ibex::SystemFactory();
    map<string, ibex::Variable const> var_map;  // Needed for translateEnodeToExprCtr

    // Construct System: add Variables
    for (Enode * e : vars) {
        string const & name = e->getCar()->getNameFull();
        DREAL_LOG_INFO << "build_system_factory: Add Variable " << name;
        auto var_it = m_var_cache.find(e);
        ibex::Variable const * var = nullptr;
        if (var_it == m_var_cache.end()) {
            // Not found
            var = new ibex::Variable(name.c_str());
            DREAL_LOG_INFO << "Added: var " << var << endl;
            m_var_cache.emplace(e, var);
        } else {
            // Found
            var = var_it->second;
        }
        var_map.emplace(name, *var);
        sf->add_var(*var);
    }
    DREAL_LOG_DEBUG << "build_system_factory: Add Variable: DONE";

    // Construct System: add constraints
    for (shared_ptr<nonlinear_constraint> const ctr : ctrs) {
        if (ctr->is_neq()) {
            continue;
        }
        DREAL_LOG_INFO << "build_system_factory: Add Constraint: " << *ctr;
        Enode * e = ctr->get_enode();
        auto p = e->getPolarity();
        assert(p == l_True || p == l_False);
        auto & m_exprctr_cache = (p == l_True) ? m_exprctr_cache_pos : m_exprctr_cache_neg;
        auto exprctr_it = m_exprctr_cache.find(e);
        ibex::ExprCtr const * exprctr = nullptr;
        if (exprctr_it == m_exprctr_cache.end()) {
            // Not found
            exprctr = translate_enode_to_exprctr(var_map, e);
            m_exprctr_cache.emplace(e, exprctr);
            DREAL_LOG_INFO << "Added: exprctr " << p << " " << *exprctr << endl;
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
    unsigned const size = s.size();
    unsigned i = 0;
    ibex::Array<ibex::ExprSymbol const> ret(size);
    for (auto const e : s) {
        string const & name = e->getCar()->getNameFull();
        ibex::Variable var(name.c_str());
        ret[i++] = (*var.symbol);
    }
    return ret;
}

contractor_ibex_fwdbwd::contractor_ibex_fwdbwd(shared_ptr<nonlinear_constraint> const ctr)
    : contractor_cell(contractor_kind::IBEX_FWDBWD, ctr->get_var_array().size()), m_ctr(ctr),
      m_numctr(ctr->get_numctr()) {
    if (!ctr->is_neq()) {
        auto ctc = get_ctc(std::this_thread::get_id(), false);
        // m_output will be copied from m_ctc->output, so no need to init here
        int const * ptr_used_var = ctc->f.used_vars();
        for (int i = 0 ; i < ctc->f.nb_used_vars(); ++i) {
            m_input.add(*ptr_used_var++);
        }
    }
}

void contractor_ibex_fwdbwd::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_ibex_fwdbwd::prune";
    auto ctc = get_ctc(std::this_thread::get_id(), true);
    if (!ctc) { return; }

    thread_local static box old_box(cs.m_box);
    if (cs.m_config.nra_proof) { old_box = cs.m_box; }
    if (m_numctr->f.nb_arg() == 0) {
        auto eval_result = m_ctr->eval(cs.m_box);
        if (eval_result.first == l_False) {
            cs.m_box.set_empty();
            return;
        } else {
            return;
        }
    }
    thread_local static ibex::IntervalVector old_iv(cs.m_box.get_values());
    old_iv = cs.m_box.get_values();
    assert(m_numctr->f.nb_arg() >= 0 && static_cast<unsigned>(m_numctr->f.nb_arg()) <= cs.m_box.size());
    DREAL_LOG_DEBUG << "Before pruning using ibex_fwdbwd(" << *m_numctr << ")";
    DREAL_LOG_DEBUG << cs.m_box;
    DREAL_LOG_DEBUG << "ibex interval = " << cs.m_box.get_values() << " (before)";
    DREAL_LOG_DEBUG << "function = " << ctc->f;
    DREAL_LOG_DEBUG << "domain   = " << ctc->d;
    ctc->contract(cs.m_box.get_values());
    DREAL_LOG_DEBUG << "ibex interval = " << cs.m_box.get_values() << " (after)";
    // cerr << output.empty() << used_constraints.empty() << " ";
    auto & new_iv = cs.m_box.get_values();
    bool changed = false;
    for (unsigned i = 0; i < cs.m_box.size(); ++i) {
        if (m_input.contain(i) && old_iv[i] != new_iv[i]) {
            cs.m_output.add(i);
            changed = true;
        }
    }
    if (changed || cs.m_box.is_empty()) {
        // only add used_constraints if there is any change
        cs.m_used_constraints.insert(m_ctr);
    }
    DREAL_LOG_DEBUG << "After pruning using ibex_fwdbwd(" << *m_numctr << ")";
    DREAL_LOG_DEBUG << cs.m_box;
    if (cs.m_config.nra_proof) {
        // ======= Proof =======
        thread_local static ostringstream ss;
        Enode const * const e = m_ctr->get_enode();
        ss << (e->getPolarity() == l_False ? "!" : "") << e;
        output_pruning_step(old_box, cs, ss.str());
        ss.str(string());
    }
    return;
}
ostream & contractor_ibex_fwdbwd::display(ostream & out) const {
    out << "contractor_ibex_fwdbwd(";
    auto const ctc = get_ctc(std::this_thread::get_id());
    if (ctc) { out << *m_numctr; }
    out << ")";
    return out;
}

contractor_ibex_newton::contractor_ibex_newton(box const & box, shared_ptr<nonlinear_constraint> const ctr)
    : contractor_cell(contractor_kind::IBEX_NEWTON, box.size()), m_ctr(ctr),
      m_numctr(ctr->get_numctr()), m_var_array(ctr->get_var_array()) {
    if (!ctr->is_neq()) {
        auto & f = m_numctr->f;
        if (f.nb_var() != f.image_dim()) {
            return;
        }
        m_ctc.reset(new ibex::CtcNewton(m_numctr->f));
        // Set up input
        ibex::BitSet const * const input = m_ctc->input;
        for (int i = input->min(); i <= input->max(); i++) {
            if ((*input)[i]) {
                m_input.add(box.get_index(m_var_array[i].name));
            }
        }
    }
}

void contractor_ibex_newton::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_ibex_newton::prune";
    if (!m_ctc) { return; }

    // ======= Proof =======
    thread_local static box old_box(cs.m_box);
    if (cs.m_config.nra_proof) { old_box = cs.m_box; }
    if (m_var_array.size() == 0) {
        auto eval_result = m_ctr->eval(cs.m_box);
        if (eval_result.first == l_False) {
            cs.m_box.set_empty();
            return;
        } else {
            return;
        }
    }
    assert(m_var_array.size() - cs.m_box.size() == 0);
    DREAL_LOG_DEBUG << "Before pruning using ibex_newton(" << *m_numctr << ")";
    DREAL_LOG_DEBUG << cs.m_box;
    DREAL_LOG_DEBUG << "ibex interval = " << cs.m_box.get_values() << " (before)";
    DREAL_LOG_DEBUG << "function = " << m_ctc->f;
    m_ctc->contract(cs.m_box.get_values());
    DREAL_LOG_DEBUG << "ibex interval = " << cs.m_box.get_values() << " (after)";
    // Set up output
    ibex::BitSet const * const ctc_output = m_ctc->output;
    bool changed = false;
    for (int i = ctc_output->min(); i <= ctc_output->max(); i++) {
        if ((*ctc_output)[i]) {
            cs.m_output.add(cs.m_box.get_index(m_var_array[i].name));
            changed = true;
        }
    }
    if (changed) {
        // only add used_constraints if there is any change
        cs.m_used_constraints.insert(m_ctr);
    }
    DREAL_LOG_DEBUG << "After pruning using ibex_newton(" << *m_numctr << ")";
    DREAL_LOG_DEBUG << cs.m_box;

    // ======= Proof =======
    if (cs.m_config.nra_proof) {
        thread_local static ostringstream ss;
        Enode const * const e = m_ctr->get_enode();
        ss << (e->getPolarity() == l_False ? "!" : "") << e;
        output_pruning_step(old_box, cs, ss.str());
        ss.str(string());
    }
    return;
}
ostream & contractor_ibex_newton::display(ostream & out) const {
    out << "contractor_ibex_newton(";
    if (m_ctc) { out << *m_numctr; }
    out << ")";
    return out;
}

contractor_ibex_hc4::contractor_ibex_hc4(vector<Enode *> const & vars, vector<shared_ptr<nonlinear_constraint>> const & ctrs)
    : contractor_cell(contractor_kind::IBEX_HC4), m_ctrs(ctrs) {
    // Trivial Case
    if (m_ctrs.size() == 0) { return; }
    unsigned index = 0;
    ibex::Array<ibex::NumConstraint> cps(ctrs.size());
    for (shared_ptr<nonlinear_constraint> numctr : ctrs) {
        cps.set_ref(index++, *(numctr->get_numctr()));
    }
    m_ctc.reset(new ibex::CtcHC4(cps));

    // Setup m_input
    m_input = ibex::BitSet::empty(vars.size());
    unordered_map<Enode*, unsigned> enode_to_id;
    for (unsigned i = 0; i < vars.size(); ++i) {
        enode_to_id.emplace(vars[i], i);
    }
    for (auto const ctr : ctrs) {
        for (auto const var : ctr->get_vars()) {
            m_input.add(enode_to_id[var]);
        }
    }

    for (shared_ptr<nonlinear_constraint> ctr : ctrs) {
        unordered_set<Enode*> const & vars_in_ctr = ctr->get_enode()->get_vars();
        m_vars_in_ctrs.insert(vars_in_ctr.begin(), vars_in_ctr.end());
    }

    DREAL_LOG_INFO << "contractor_ibex_hc4: DONE" << endl;
}

void contractor_ibex_hc4::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_ibex_hc4::prune";

    if (!m_ctc) { return; }

    // TODO(soonhok): need to remove the following
    // setup input
    for (Enode * var : m_vars_in_ctrs) {
        m_input.add(cs.m_box.get_index(var));
    }

    thread_local static box old_box(cs.m_box);
    old_box = cs.m_box;
    m_ctc->contract(cs.m_box.get_values());
    // setup output
    vector<bool> diff_dims = cs.m_box.diff_dims(old_box);
    bool changed = false;
    for (unsigned i = 0; i < diff_dims.size(); i++) {
        if (diff_dims[i]) {
            cs.m_output.add(i);
            changed = true;
        }
    }
    if (changed) {
        cs.m_used_constraints.insert(m_ctrs.begin(), m_ctrs.end());
    }

    // ======= Proof =======
    if (cs.m_config.nra_proof) {
        thread_local static ostringstream ss;
        for (auto const & ctr : m_ctrs) {
            Enode const * const e = ctr->get_enode();
            ss << (e->getPolarity() == l_False ? "!" : "") << e << ";";
        }
        output_pruning_step(old_box, cs, ss.str());
        ss.str(string());
    }
    return;
}
ostream & contractor_ibex_hc4::display(ostream & out) const {
    out << "contractor_ibex_hc4(";
    for (unsigned i = 0; i < m_ctrs.size(); i++) {
        out << *m_ctrs[i] << ", ";
    }
    out << ")";
    return out;
}

contractor_ibex_polytope::contractor_ibex_polytope(double const prec, vector<Enode *> const & vars, vector<shared_ptr<nonlinear_constraint>> const & ctrs)
    : contractor_cell(contractor_kind::IBEX_POLYTOPE), m_ctrs(ctrs), m_prec(prec) {
    // Trivial Case
    if (m_ctrs.size() == 0) { return; }
    m_sf.reset(build_system_factory(vars, m_ctrs));
    try {
        m_sys.reset(new ibex::System(*m_sf));
    } catch (ibex::EmptySystemException & e) {
        DREAL_LOG_INFO << "contractor_ibex_polytope::contractor_ibex_polytope: empty ibex::system";
        return;
    }

    unsigned index = 0;

    ibex::Array<ibex::Ctc> ctc_list(2);

    m_sys_eqs = square_eq_sys(*m_sys);
    if (m_sys_eqs) {
        DREAL_LOG_INFO << "contractor_ibex_polytope: SQUARE SYSTEM";
        unique_ptr<ibex::CtcNewton> ctc_newton(new ibex::CtcNewton(m_sys_eqs->f));
        ctc_list.set_ref(index++, *ctc_newton);
        m_sub_ctcs.push_back(move(ctc_newton));
    }

    m_lrc.reset(new ibex::LinearRelaxCombo(*m_sys, ibex::LinearRelaxCombo::XNEWTON));
    unique_ptr<ibex::CtcPolytopeHull> ctc_ph(new ibex::CtcPolytopeHull(*m_lrc, ibex::CtcPolytopeHull::ALL_BOX));
    unique_ptr<ibex::CtcHC4> ctc_hc4(new ibex::CtcHC4(m_sys->ctrs, m_prec));
    unique_ptr<ibex::CtcCompo> ctc_combo(new ibex::CtcCompo(*ctc_ph, *ctc_hc4));
    unique_ptr<ibex::CtcFixPoint> ctc_fp(new ibex::CtcFixPoint(*ctc_combo));
    ctc_list.set_ref(index++, *ctc_fp);
    m_sub_ctcs.push_back(move(ctc_ph));
    m_sub_ctcs.push_back(move(ctc_hc4));
    m_sub_ctcs.push_back(move(ctc_combo));
    m_sub_ctcs.push_back(move(ctc_fp));

    ctc_list.resize(index);
    m_ctc.reset(new ibex::CtcCompo(ctc_list));

    // Setup m_input
    m_input = ibex::BitSet::empty(vars.size());
    unordered_map<Enode*, unsigned> enode_to_id;
    for (unsigned i = 0; i < vars.size(); ++i) {
        enode_to_id.emplace(vars[i], i);
    }
    for (auto const ctr : ctrs) {
        for (auto const var : ctr->get_vars()) {
            m_input.add(enode_to_id[var]);
        }
    }

    for (shared_ptr<nonlinear_constraint> ctr : ctrs) {
        unordered_set<Enode*> const & vars_in_ctr = ctr->get_enode()->get_vars();
        m_vars_in_ctrs.insert(vars_in_ctr.begin(), vars_in_ctr.end());
    }

    DREAL_LOG_INFO << "contractor_ibex_polytope: DONE" << endl;
}

contractor_ibex_polytope::~contractor_ibex_polytope() {
    if (m_sys_eqs && m_sys_eqs != m_sys.get()) { delete m_sys_eqs; }
    for (auto p : m_exprctr_cache_pos) {
        ibex::cleanup(p.second->e, false);
        delete p.second;
    }
    for (auto p : m_exprctr_cache_neg) {
        ibex::cleanup(p.second->e, false);
        delete p.second;
    }
    for (auto p : m_var_cache) {
        ibex::Variable const * var = p.second;
        ibex::ExprSymbol* symbol = var->symbol;
        delete var;
        delete symbol;
    }
}

void contractor_ibex_polytope::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_ibex_polytope::prune";
    if (!m_ctc) { return; }

    // TODO(soonhok): need to remove the following
    // setup input
    for (Enode * var : m_vars_in_ctrs) {
        m_input.add(cs.m_box.get_index(var));
    }
    thread_local static box old_box(cs.m_box);
    old_box = cs.m_box;
    m_ctc->contract(cs.m_box.get_values());

    // setup output
    vector<bool> diff_dims = cs.m_box.diff_dims(old_box);
    for (unsigned i = 0; i < diff_dims.size(); i++) {
        if (diff_dims[i]) {
            cs.m_output.add(i);
        }
    }

    if (!diff_dims.empty()) {
        cs.m_used_constraints.insert(m_ctrs.begin(), m_ctrs.end());
    }

    // ======= Proof =======
    if (cs.m_config.nra_proof) {
        thread_local static ostringstream ss;
        for (auto const & ctr : m_ctrs) {
            Enode const * const e = ctr->get_enode();
            ss << (e->getPolarity() == l_False ? "!" : "") << e << ";";
        }
        output_pruning_step(old_box, cs, ss.str());
        ss.str(string());
    }
    return;
}
ostream & contractor_ibex_polytope::display(ostream & out) const {
    out << "contractor_ibex_polytope(";
    for (unsigned i = 0; i < m_ctrs.size(); i++) {
        out << *m_ctrs[i] << ", ";
    }
    out << ")";
    return out;
}

contractor mk_contractor_ibex_fwdbwd(shared_ptr<nonlinear_constraint> const ctr, bool const use_cache) {
    if (!use_cache) {
        return contractor(make_shared<contractor_ibex_fwdbwd>(ctr));
    }
    static unordered_map<shared_ptr<nonlinear_constraint>, contractor> ibex_fwdbwd_ctc_cache;
    auto const it = ibex_fwdbwd_ctc_cache.find(ctr);
    if (it == ibex_fwdbwd_ctc_cache.end()) {
        contractor ctc(make_shared<contractor_ibex_fwdbwd>(ctr));
        ibex_fwdbwd_ctc_cache.emplace(ctr, ctc);
        return ctc;
    } else {
        return it->second;
    }
}

contractor mk_contractor_ibex_newton(box const & box, shared_ptr<nonlinear_constraint> const ctr) {
    return contractor(make_shared<contractor_ibex_newton>(box, ctr));
}
contractor mk_contractor_ibex_hc4(vector<Enode *> const & vars, vector<shared_ptr<nonlinear_constraint>> const & ctrs) {
    return contractor(make_shared<contractor_ibex_hc4>(vars, ctrs));
}
contractor mk_contractor_ibex_polytope(double const prec, vector<Enode *> const & vars, vector<shared_ptr<nonlinear_constraint>> const & ctrs) {
    return contractor(make_shared<contractor_ibex_polytope>(prec, vars, ctrs));
}
}  // namespace dreal
