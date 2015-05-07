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

#include "dsolvers/nra_solver.h"
#include <gflags/gflags.h>
#include <algorithm>
#include <iomanip>
#include <iostream>
#include <limits>
#include <memory>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <tuple>
#include <utility>
#include <vector>
#include "./config.h"
#include "ibex/ibex.h"
#include "util/box.h"
#include "util/constraint.h"
#include "contractor/contractor.h"
#include "util/ibex_enode.h"
#include "util/logging.h"
#include "util/stat.h"
#include "json/json.hpp"

using ibex::IntervalVector;
using nlohmann::json;
using std::boolalpha;
using std::get;
using std::logic_error;
using std::numeric_limits;
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
    m_need_init = true;
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check" assertLit adds a literal(e) to
// stack of asserted literals.
bool nra_solver::assertLit(Enode * e, bool reason) {
    if (config.nra_stat) { m_stat.increase_assert(); }

    if (m_need_init) {
        m_box.constructFromLiterals(m_lits);
        m_ctrs = initialize_constraints();
        m_need_init = false;
    }

    DREAL_LOG_INFO << "nra_solver::assertLit: " << e
                   << ", reason: " << boolalpha << reason
                   << ", polarity: " << e->getPolarity().toInt()
                   << ", deduced: " << e->isDeduced()
                   << ", getDeduced: " << e->getDeduced().toInt()
                   << ", getIndex: " << e->getDedIndex()
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
    auto it = m_ctr_map.find(make_pair(e, e->getPolarity() == l_True));
    if (it != m_ctr_map.end()) {
        m_stack.push_back(it->second);
    } else if (e->isForallT()) {
    } else if (e->isIntegral() && e->getPolarity() == l_False) {
        return true;
    } else {
        DREAL_LOG_FATAL << "Unknown literal "
                        << (e->getPolarity() == l_False ? "!" : "")
                        << e << " is asserted";
        throw std::logic_error("unknown literal is asserted");
    }
    return true;
}

// Given a list of theory literals (vector<Enode *>), build a list of constraints vector<constraint *>
std::vector<constraint *> nra_solver::initialize_constraints() {
    std::vector<constraint *> ctrs;

    std::vector<integral_constraint> ints;
    std::vector<forallt_constraint> invs;
    for (Enode * l : m_lits) {
        // Partition ODE-related constraint into integrals and forallTs
        if (l->isIntegral()) {
            integral_constraint ic = mk_integral_constraint(l, egraph.flow_maps);
            ints.push_back(ic);
        } else if (l->isForallT()) {
            forallt_constraint fc = mk_forallt_constraint(l);
            invs.push_back(fc);
        } else {
            // Collect Nonlinear constraints.
            nonlinear_constraint * nc_pos = new nonlinear_constraint(l, l_True);
            nonlinear_constraint * nc_neg = new nonlinear_constraint(l, l_False);
            DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect NonlinearConstraint (+): " << *nc_pos;
            DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect NonlinearConstraint (-): " << *nc_neg;
            ctrs.push_back(nc_pos);
            ctrs.push_back(nc_neg);
            m_ctr_map.emplace(make_pair(l, true),  nc_pos);
            m_ctr_map.emplace(make_pair(l, false), nc_neg);
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
            }
        }
        ode_constraint * oc = new ode_constraint(ic, local_invs);
        ctrs.push_back(oc);
        m_ctr_map.emplace(make_pair(ic.get_enodes()[0], true), oc);
        DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect ODEConstraint: " << *oc;
    }
    return ctrs;
}

contractor nra_solver::build_contractor(box const & box, scoped_vec<constraint *> const &ctrs, bool const complete) {
    vector<nonlinear_constraint const *> nl_ctrs;
    vector<contractor> nl_ctcs;
    nl_ctcs.reserve(ctrs.size());
    vector<contractor> nl_eval_ctcs;
    nl_eval_ctcs.reserve(ctrs.size());
    vector<contractor> ode_ctcs;
    ode_ctcs.reserve(ctrs.size());
    // Add contractor_sample if --sample option is used
    if (config.nra_sample > 0 && complete) {
        nl_ctcs.push_back(mk_contractor_sample(config.nra_sample, ctrs.get_vec()));
    }
    for (constraint * const ctr : ctrs.get_reverse()) {
        if (ctr->get_type() == constraint_type::Nonlinear) {
            nonlinear_constraint const * const nl_ctr = dynamic_cast<nonlinear_constraint *>(ctr);
            if (nl_ctr->get_numctr()) {
                nl_ctcs.push_back(mk_contractor_ibex_fwdbwd(box, nl_ctr));
                nl_ctrs.push_back(nl_ctr);
            } else {
                // This is identity, do nothing
            }
            nl_eval_ctcs.push_back(mk_contractor_eval(box, nl_ctr));
#ifdef SUPPORT_ODE
        } else if (ctr->get_type() == constraint_type::ODE) {
            // TODO(soonhok): add heuristics to choose fwd/bwd
            // TODO(soonhok): perform ODE only for complete check
            ode_ctcs.emplace_back(
                mk_contractor_try(
                    mk_contractor_capd_fwd_full(box, dynamic_cast<ode_constraint *>(ctr), config.nra_ODE_taylor_order, config.nra_ODE_grid_size)));
            ode_ctcs.emplace_back(
                mk_contractor_try(
                    mk_contractor_capd_bwd_full(box, dynamic_cast<ode_constraint *>(ctr), config.nra_ODE_taylor_order, config.nra_ODE_grid_size)));
#endif
        }
    }
    if (config.nra_polytope) {
        nl_ctcs.push_back(mk_contractor_ibex_polytope(config.nra_precision, nl_ctrs));
    }
    nl_ctcs.push_back(mk_contractor_int());
    // Add contractor_sample if --sample option is used
    if (config.nra_aggressive > 0 && complete) {
        nl_ctcs.push_back(mk_contractor_sample(config.nra_aggressive, ctrs.get_vec()));
    }

    auto term_cond = [this](dreal::box const & old_box, dreal::box const & new_box) {
        if (new_box.max_diam() < config.nra_precision) {
            return true;
        }
        double const threshold = 0.01;
        // If there is a dimension which is improved more than
        // threshold, we stop the current fixed-point computation.
        for (unsigned i = 0; i < old_box.size(); i++) {
            double const new_box_i = new_box[i].diam();
            double const old_box_i = old_box[i].diam();
            if (new_box_i == numeric_limits<double>::infinity()) {
                continue;
            }
            if (old_box_i == 0) {
                // The i-th dimension was already a point, nothing to improve.
                continue;
            }
            double const improvement = 1 - new_box_i / old_box_i;
            assert(!std::isnan(improvement));
            if (improvement >= threshold) {
                return false;
            }
        }
        return true;
    };
    return mk_contractor_fixpoint(term_cond, nl_ctcs, ode_ctcs, nl_eval_ctcs);
}

// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint() {
    if (m_need_init) {
        m_box.constructFromLiterals(m_lits);
        m_ctrs = initialize_constraints();
        m_need_init = false;
    }
    if (config.nra_stat) { m_stat.increase_push(); }
    DREAL_LOG_INFO << "nra_solver::pushBacktrackPoint " << m_stack.size();
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
    m_box.assign_to_enode();
    m_used_constraint_vec.pop();
    m_stack.pop();
}

box icp_loop(box b, contractor const & ctc, SMTConfig & config) {
    vector<box> solns;
    stack<box> box_stack;
    box_stack.push(b);
    do {
        DREAL_LOG_INFO << "icp_loop()"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.top();
        box_stack.pop();
        try {
            b = ctc.prune(b, config);
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!b.is_empty()) {
            if (b.max_diam() > config.nra_precision) {
                tuple<int, box, box> splits = b.bisect();
                unsigned const i   = get<0>(splits);
                box const & first  = get<1>(splits);
                box const & second = get<2>(splits);
                if (second.is_bisectable()) {
                    box_stack.push(second);
                    box_stack.push(first);
                } else {
                    box_stack.push(first);
                    box_stack.push(second);
                }
                if (config.nra_proof) {
                    config.nra_proof_out << "[branched on "
                                         << b.get_name(i)
                                         << "]" << endl;
                }
            } else {
                config.nra_found_soln++;
                if (config.nra_multiple_soln > 1) {
                    cerr << "Find " << config.nra_found_soln << "-th solution:" << endl;
                    cerr << b << endl;
                }
                solns.push_back(b);
                if (config.nra_found_soln >= config.nra_multiple_soln) {
                    break;
                }
            }
        }
    } while (box_stack.size() > 0);
    if (solns.size() > 0) {
        return solns.back();
    } else {
        return b;
    }
}

box icp_loop_with_nc_bt(box b, contractor const & ctc, SMTConfig & config) {
    static unsigned prune_count = 0;
    stack<box> box_stack;
    stack<int> bisect_var_stack;
    box_stack.push(b);
    bisect_var_stack.push(-1);  // Dummy var
    do {
        // Loop Invariant
        assert(box_stack.size() == bisect_var_stack.size());
        DREAL_LOG_INFO << "new_icp_loop()"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.top();
        try {
            b = ctc.prune(b, config);
        } catch (contractor_exception & e) {
            // Do nothing
        }
        prune_count++;
        box_stack.pop();
        bisect_var_stack.pop();
        if (!b.is_empty()) {
            // SAT
            if (b.max_diam() > config.nra_precision) {
              config.inc_icp_decisions();
                tuple<int, box, box> splits = b.bisect();
                unsigned const index = get<0>(splits);
                box const & first    = get<1>(splits);
                box const & second   = get<2>(splits);
                if (second.is_bisectable()) {
                    box_stack.push(second);
                    box_stack.push(first);
                } else {
                    box_stack.push(first);
                    box_stack.push(second);
                }
                bisect_var_stack.push(index);
                bisect_var_stack.push(index);
            } else {
                break;
            }
        } else {
            // UNSAT
            while (box_stack.size() > 0) {
                assert(box_stack.size() == bisect_var_stack.size());
                int bisect_var = bisect_var_stack.top();
                ibex::BitSet const & input = ctc.input();
                DREAL_LOG_DEBUG << ctc;
                if (!input[bisect_var]) {
                    box_stack.pop();
                    bisect_var_stack.pop();
                } else {
                    break;
                }
            }
        }
    } while (box_stack.size() > 0);
    DREAL_LOG_DEBUG << "prune count = " << prune_count;
    return b;
}

void nra_solver::handle_sat_case(box const & b) const {
    // SAT
    DREAL_LOG_FATAL << "Solution:";
    DREAL_LOG_FATAL << b;
    // --proof option
    if (config.nra_proof) {
        config.nra_proof_out.close();
        config.nra_proof_out.open(config.nra_proof_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
        display(config.nra_proof_out, b, !config.nra_readable_proof, true);
    }
    // --model option
    if (config.nra_model) {
        config.nra_model_out.open(config.nra_model_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
        if (config.nra_model_out.fail()) {
            cout << "Cannot create a file: " << config.nra_model_out_name << endl;
            exit(1);
        }
        display(config.nra_model_out, b, false, true);
    }
#ifdef SUPPORT_ODE
    // --visualize option
    if (config.nra_json) {
        json traces = {};
        // Need to run ODE pruning operator once again to generate a trace
        for (constraint * const ctr : m_stack) {
            if (ctr->get_type() == constraint_type::ODE) {
                contractor_capd_fwd_full fwd_full(b, dynamic_cast<ode_constraint *>(ctr), config.nra_ODE_taylor_order, config.nra_ODE_grid_size);
                json trace = fwd_full.generate_trace(b, config);
                traces.push_back(trace);
            }
        }
        json vis_json;
        vis_json["traces"] = traces;
        config.nra_json_out << vis_json.dump() << endl;;
    }
#endif
    // For API call
    b.assign_to_enode();
    return;
}

void nra_solver::handle_deduction() {
    for (Enode * const l : m_lits) {
        if (l->getPolarity() == l_Undef && !l->isDeduced()) {
            auto it = m_ctr_map.find(make_pair(l, true));
            if (it != m_ctr_map.end()) {
                constraint * ctr = it->second;
                nonlinear_constraint const * const nl_ctr = dynamic_cast<nonlinear_constraint *>(ctr);
                if (nl_ctr) {
                    pair<lbool, ibex::Interval> p = nl_ctr->eval(m_box);
                    if (p.first == l_False) {
                        // We know that this literal has to be false;
                        l->setDeduced(l_False, id);
                        deductions.push_back(l);
                        DREAL_LOG_INFO << "Deduced: " << *nl_ctr << "\t" << p.first << "\t" << p.second;
                    } else if (p.first == l_True) {
                        // We know that this literal has to be true;
                        l->setDeduced(l_True, id);
                        deductions.push_back(l);
                        DREAL_LOG_INFO << "Deduced: " << *nl_ctr << "\t" << p.first << "\t" << p.second;
                    }
                }
            }
        }
    }
}

// Check for consistency.
// If flag is set make sure you run a complete check
bool nra_solver::check(bool complete) {
    if (config.nra_stat) { m_stat.increase_check(complete); }
    if (m_stack.size() == 0) { return true; }
    DREAL_LOG_INFO << "nra_solver::check(complete = " << boolalpha << complete << ")"
                   << "stack size = " << m_stack.size();
    double const prec = config.nra_precision;
    m_ctc = build_contractor(m_box, m_stack, complete);
    try {
        m_box = m_ctc.prune(m_box, config);
    } catch (contractor_exception & e) {
        // Do nothing
    }
    if (!m_box.is_empty() && m_box.max_diam() > prec && complete) {
        m_box = icp_loop(m_box, m_ctc, config);
    }
    bool result = !m_box.is_empty();
    DREAL_LOG_INFO << "nra_solver::check: result = " << boolalpha << result;
    for (constraint const * ctr : m_ctc.used_constraints()) {
        m_used_constraint_vec.push_back(ctr);
    }
    if (!result) {
        explanation = generate_explanation(m_used_constraint_vec);
    } else {
        if (!complete && config.sat_theory_propagation) {
            handle_deduction();
        }
        if (complete) {
            handle_sat_case(m_box);
        }
    }
    DREAL_LOG_DEBUG << "nra_solver::check(" << (complete ? "complete" : "incomplete") << ") = " << result;
    return result;
}

vector<Enode *> nra_solver::generate_explanation(scoped_vec<constraint const *> const & ctr_vec) {
    unordered_set<Enode *> bag;
    for (constraint const * ctr : ctr_vec) {
        vector<Enode *> const & enodes_in_ctr = ctr->get_enodes();
        for (Enode * const e : enodes_in_ctr) {
            if (e->hasPolarity()) {
                bag.insert(e);
            }
        }
    }
    vector<Enode *> exps;
    copy(bag.begin(), bag.end(), back_inserter(exps));
    std::sort(exps.begin(), exps.end(), [](Enode const * const e1, Enode const * const e2) {
            return e1->getId() < e2->getId();
        });
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
