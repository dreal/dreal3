/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include <gflags/gflags.h>
#include <algorithm>
#include <iomanip>
#include <iostream>
#include <memory>
#include <sstream>
#include <stack>
#include <string>
#include <utility>
#include <vector>
#include "dsolvers/nra_solver.h"
#include "ibex/ibex.h"
#include "util/box.h"
#include "util/constraint.h"
#include "util/contractor.h"
#include "util/ibex_enode.h"
#include "util/logging.h"
#include "util/stat.h"

using ibex::IntervalVector;
using std::boolalpha;
using std::logic_error;
using std::pair;
using std::stack;
using std::vector;

namespace dreal {
using std::cout;
using std::endl;
nra_solver::nra_solver(const int i, const char * n, SMTConfig & c, Egraph & e, SStore & t,
                       vector<Enode *> & x, vector<Enode *> & d, vector<Enode *> & s)
    : OrdinaryTSolver(i, n, c, e, t, x, d, s), m_box(vector<Enode*>({})) {
    if (c.nra_precision == 0.0) c.nra_precision = 0.001;
}

nra_solver::~nra_solver() {
    for (auto it_ctr : m_ctrs) {
        delete it_ctr;
    }
    if (config.nra_stat) {
        cout << m_stat << endl;
    }
}

// `inform` sets up env (mapping from variables(enode) in literals to their [lb, ub])
lbool nra_solver::inform(Enode * e) {
    DREAL_LOG_INFO << "nra_solver::inform: " << e;
    // Collect Literal
    m_lits.push_back(e);
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check" assertLit adds a literal(e) to
// stack of asserted literals.
bool nra_solver::assertLit(Enode * e, bool reason) {
    if (config.nra_stat) { m_stat.increase_assert(); }
    DREAL_LOG_INFO << "nra_solver::assertLit: " << e
                   << ", reason: " << boolalpha << reason
                   << ", polarity: " << e->getPolarity().toInt()
                   << ", level: " << m_stack.size()
                   << ", ded.size = " << deductions.size();
    (void)reason;
    assert(e);
    assert(belongsToT(e));
    assert(e->hasPolarity());
    assert(e->getPolarity() == l_False || e->getPolarity() == l_True);
    if (e->isDeduced() && e->getPolarity() == e->getDeduced() && e->getDedIndex() == id) {
        DREAL_LOG_INFO << "nra_solver::assertLit: " << e << " is deduced";
        return true;
    }
    if (m_ctr_map.find(e) != m_ctr_map.end()) {
        m_stack.push_back(m_ctr_map.at(e));
    }
    return true;
}

// Given a list of theory literals (vector<Enode *>), build a list of constraints vector<constraint *>
std::vector<constraint *> nra_solver::initialize_constraints() {
    std::vector<constraint *> ctrs;

    // Collect Algebrac constraints.
    // Partition ODE-related constraint into integrals and forallTs
    std::vector<integral_constraint> ints;
    std::vector<forallt_constraint> invs;
    for (Enode * l : m_lits) {
        if (l->isIntegral()) {
            integral_constraint ic = mk_integral_constraint(l, egraph.flow_maps);
            ints.push_back(ic);
        } else if (l->isForallT()) {
            forallt_constraint fc = mk_forallt_constraint(l);
            invs.push_back(fc);
        } else {
            algebraic_constraint * ac = new algebraic_constraint(l);
            DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect AlgebraicConstraint: " << *ac;
            ctrs.push_back(ac);
            m_ctr_map.emplace(l, ac);
        }
    }
    // Attach the corresponding forallT literals to integrals
    for (integral_constraint ic : ints) {
        std::vector<forallt_constraint> local_invs;
        for (forallt_constraint fc : invs) {
            // Link ForallTConstraint fc with IntegralConstraint ic, if
            //    fc.flow == ic.flow
            //    vars(fc.inv) \subseteq ic.vars_t
            if (fc.get_flow_id() == ic.get_flow_id()) {
                unordered_set<Enode *> vars_in_fc = fc.get_inv()->get_vars();
                bool const included = all_of(vars_in_fc.begin(), vars_in_fc.end(),
                       [&ic](Enode const * var_in_fc) {
                           vector<Enode *> const & vars_t_in_ic = ic.get_vars_t();
                           return find(vars_t_in_ic.begin(), vars_t_in_ic.end(), var_in_fc) != vars_t_in_ic.end();
                       });
                if (included) {
                    local_invs.push_back(fc);
                }
                ode_constraint * oc = new ode_constraint(ic, local_invs);
                ctrs.push_back(oc);
                m_ctr_map.emplace(ic.get_enodes()[0], oc);
                DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect ODEConstraint: " << *oc;
            }
        }
    }
    return ctrs;
}

contractor nra_solver::build_contractor(box const & box, scoped_vec<constraint *> const &ctrs) {
    vector<algebraic_constraint const *> alg_ctrs;
    vector<contractor> alg_ctcs;
    alg_ctcs.reserve(ctrs.size());
    vector<contractor> ode_ctcs;
    ode_ctcs.reserve(ctrs.size());
    for (constraint * const ctr : ctrs) {
        if (ctr->get_type() == constraint_type::Algebraic) {
            algebraic_constraint const * const alg_ctr = dynamic_cast<algebraic_constraint *>(ctr);
            alg_ctcs.emplace_back(make_shared<contractor_ibex_fwdbwd>(box, alg_ctr));
            alg_ctrs.push_back(alg_ctr);
        } else if (ctr->get_type() == constraint_type::ODE) {
            ode_ctcs.emplace_back(make_shared<contractor_capd_fwd_full>(box, dynamic_cast<ode_constraint *>(ctr), config.nra_ODE_taylor_order, config.nra_ODE_grid_size));
        }
    }

    auto term_cond = [](dreal::box const & old_box, dreal::box const & new_box) {
        double const threshold = 0.05;
        double const new_volume = new_box.volume();
        double const old_volume = old_box.volume();
        if (old_volume == 0.0) return true;
        double const improvement = 1.00 - (new_volume / old_volume);
        return improvement < threshold;
    };

    alg_ctcs.push_back(mk_contractor_ibex(config.nra_precision, box, alg_ctrs));
    return mk_contractor_fixpoint(config.nra_precision, term_cond, alg_ctcs, ode_ctcs);
}

// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint() {
    if (config.nra_stat) { m_stat.increase_push(); }
    DREAL_LOG_INFO << "nra_solver::pushBacktrackPoint " << m_stack.size();
    if (m_stack.size() == 0) {
        m_box.constructFromLiterals(m_lits);
        m_ctrs = initialize_constraints();
    }
    m_stack.push();
    m_used_constraint_vec.push();
    m_boxes.push_back(m_box);
    m_boxes.push();
}

// Restore a previous state. You can now retrieve the size of the
// stack when you pushed the last backtrack point. You have to
// implement the necessary backtrack operations (see for instance
// backtrackToStackSize() in EgraphSolver) Also make sure you clean
// the deductions you did not communicate
void nra_solver::popBacktrackPoint() {
    if (config.nra_stat) { m_stat.increase_pop(); }
    DREAL_LOG_INFO << "nra_solver::popBacktrackPoint\t m_stack.size()      = " << m_stack.size();
    m_boxes.pop();
    m_box = m_boxes.last();
    m_used_constraint_vec.pop();
    m_stack.pop();
}

// Check for consistency.
// If flag is set make sure you run a complete check
bool nra_solver::check(bool complete) {
    if (config.nra_stat) { m_stat.increase_check(complete); }
    if (m_stack.size() == 0) {
        return true;
    }
    DREAL_LOG_INFO << "nra_solver::check(complete = " << boolalpha << complete << ")";
    double const prec = config.nra_precision;
    m_ctc = build_contractor(m_box, m_stack);
    m_box = m_ctc.prune(m_box);
    if (complete && !m_box.is_empty() && m_box.max_diam() > prec) {
        stack<box> box_stack;
        box_stack.push(m_box);
        while (box_stack.size() > 0) {
            DREAL_LOG_INFO << "nra_solver::check(complete = " << boolalpha << complete << ")"
                           << "\t" << "box stack Size = " << box_stack.size();
            m_box = box_stack.top();
            box_stack.pop();
            m_box = m_ctc.prune(m_box);
            if (!m_box.is_empty()) {
                if (m_box.max_diam() > prec) {
                    pair<box, box> splits = m_box.split();
                    box_stack.push(splits.first);
                    box_stack.push(splits.second);
                } else {
                    break;
                }
            }
        }
    }
    bool result = !m_box.is_empty();
    DREAL_LOG_INFO << "nra_solver::check: result = " << boolalpha << result;
    for (constraint const * ctr : m_ctc.used_constraints()) {
        m_used_constraint_vec.push_back(ctr);
    }
    if (!result) {
        explanation = generate_explanation(m_used_constraint_vec);
        // DREAL_LOG_FATAL << "nra_solver::check: explanation size = " << explanation.size();
    } else if (complete) {
        // SAT
        DREAL_LOG_FATAL << "Solution:";
        DREAL_LOG_FATAL << m_box;
        // --proof option
        if (config.nra_proof) {
            config.nra_proof_out.close();
            config.nra_proof_out.open(config.nra_proof_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
            m_box.display_old_style_model(config.nra_proof_out);
        }
        // --model option
        if (config.nra_model) {
            config.nra_model_out.open (config.nra_model_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);            if (config.nra_model_out.fail()) {
                cout << "Cannot create a file: " << config.nra_model_out_name << endl;
                exit(1);
            }
            m_box.display_old_style_model(config.nra_model_out);
        }
    }
    return result;
}

vector<Enode *> nra_solver::generate_explanation(scoped_vec<constraint const *> const & ctr_vec) {
    vector<Enode *> exps;
    unordered_set<Enode *> bag;
    for (constraint const * ctr : ctr_vec) {
        vector<Enode *> const & enodes_in_ctr = ctr->get_enodes();
        bag.insert(enodes_in_ctr.begin(), enodes_in_ctr.end());
    }
    copy(bag.begin(), bag.end(), back_inserter(exps));
    return exps;
}

// Return true if the enode belongs to this theory. You should examine
// the structure of the node to see if it matches the theory operators
bool nra_solver::belongsToT(Enode * e) {
    (void)e;
    assert(e);
    return true;
}

// Copy the model into enode's data
void nra_solver::computeModel() {
    DREAL_LOG_DEBUG << "nra_solver::computeModel" << endl;
}
}  // namespace dreal
