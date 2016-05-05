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
#include <exception>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>
#include "dsolvers/nra_solver.h"
#include "./config.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "ibex/ibex.h"
#include "icp/icp.h"
#include "icp/icp_simulation.h"
#include "json/json.hpp"
#include "util/box.h"
#include "util/ibex_enode.h"
#include "util/logging.h"
#include "util/stat.h"
#include "util/strategy.h"
#ifdef USE_GLPK
#include "util/glpk_wrapper.h"
#include "icp/lp_icp.h"
#endif

using ibex::IntervalVector;
using nlohmann::json;
using std::all_of;
using std::boolalpha;
using std::cerr;
using std::cout;
using std::dynamic_pointer_cast;
using std::endl;
using std::get;
using std::logic_error;
using std::make_pair;
using std::make_shared;
using std::map;
using std::numeric_limits;
using std::ofstream;
using std::pair;
using std::runtime_error;
using std::shared_ptr;
using std::sort;
using std::string;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {
nra_solver::nra_solver(const int i, const char * n, SMTConfig & c, Egraph & e, SStore & t,
                       vector<Enode *> & x, vector<Enode *> & d, vector<Enode *> & s)
    : OrdinaryTSolver(i, n, c, e, t, x, d, s), m_box(vector<Enode*>({})) {
    if (c.nra_precision == 0.0) c.nra_precision = 0.001;
}

nra_solver::~nra_solver() {
    DREAL_LOG_INFO << "~nra_solver()";
    if (config.nra_use_stat) {
        cout << config.nra_stat << endl;
    }
}

// `inform` sets up env (mapping from variables(enode) in literals to their [lb, ub])
lbool nra_solver::inform(Enode * e) {
    DREAL_LOG_INFO << "nra_solver::inform: " << e;
    // Collect Literal
    m_lits.push_back(e);
    m_need_init = true;
    return l_Undef;
/*
    if (!e->isIntegral() && !e->isForall() && !e->isForallT() ) {
        cout << "Before slacking: "<< e << endl;
        e = slack_constraint(e);
        cout << "After slacking: "<< e << endl;
    }
    m_lits.push_back(e);
    for (auto l : slack_ctrs_tmp) {
        l -> setPolarity(l_True);
        m_lits.push_back(l);
        cout << "Collected slack equality: "<< l << endl;
    }
    slack_ctrs_tmp.clear(); //sorry for the temporary hack. slack_ctrs_tmp keeps the slack equalities for this constraint.
    m_need_init = true;
    return l_Undef;
*/
}

// Simplify box b using a constraint e.
// Return l_True   if a constriant is used and not needed after this.
// Return l_False  if a constriant is used and but still needed after this.
// Otherwise, return l_Undef
static lbool simplify(Enode * e, lbool p, box & b) {
    if (e->isNot()) {
        return simplify(e->get1st(), !p, b);
    }
    if (e->getArity() != 2) {
        return l_Undef;
    }
    Enode * const first = e->get1st();
    Enode * const second = e->get2nd();
    if ((p == l_True && (e->isGt() || e->isGeq())) ||
        (p == l_False && (e->isLt() || e->isLeq()))) {
        if (first->isVar() && second->isConstant()) {
            // v >= c
            auto & iv = b[first];
            iv &= ibex::Interval(second->getValue(), iv.ub());
            if (iv.is_empty()) { b.set_empty(); }
            return l_True;
        } else if (first->isConstant() && second->isVar()) {
            // c >= v
            auto & iv = b[second];
            iv &= ibex::Interval(iv.lb(), first->getValue());
            if (iv.is_empty()) { b.set_empty(); }
            return l_True;
        }
    } else if ((p == l_True && (e->isLt() || e->isLeq())) ||
               (p == l_False && (e->isGt() || e->isGeq()))) {
        if (first->isVar() && second->isConstant()) {
            // v <= c
            auto & iv = b[first];
            iv &= ibex::Interval(iv.lb(), second->getValue());
            if (iv.is_empty()) { b.set_empty(); }
            return l_True;
        } else if (first->isConstant() && second->isVar()) {
            // c <= v
            auto & iv = b[second];
            iv &= ibex::Interval(first->getValue(), iv.ub());
            if (iv.is_empty()) { b.set_empty(); }
            return l_True;
        }
    } else if (p == l_True && e->isEq()) {
        if (first->isVar() && second->isConstant()) {
            // v == c
            auto & iv = b[first];
            iv &= ibex::Interval(second->getValue(), second->getValue());
            if (iv.is_empty()) { b.set_empty(); }
            return l_True;
        } else if (first->isConstant() && second->isVar()) {
            // c == v
            auto & iv = b[second];
            iv &= ibex::Interval(first->getValue(), first->getValue());
            if (iv.is_empty()) { b.set_empty(); }
            return l_True;
        } else if (first->isVar() && second->isVar()) {
            // v1 == v2
            auto & iv_1 = b[first];
            auto & iv_2 = b[second];
            iv_1 &= iv_2;
            iv_2 = iv_1;
            if (iv_1.is_empty()) {
                b.set_empty();
                return l_True;
            }
            return l_False;
        }
    }
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check" assertLit adds a literal(e) to
// stack of asserted literals.
bool nra_solver::assertLit(Enode * e, bool reason) {
    DREAL_LOG_INFO << "nra_solver::assertLit: " << e
                   << ", reason: " << boolalpha << reason
                   << ", polarity: " << e->getPolarity().toInt()
                   << ", deduced: " << e->isDeduced()
                   << ", getDeduced: " << e->getDeduced().toInt()
                   << ", getIndex: " << e->getDedIndex()
                   << ", level: " << m_stack.size()
                   << ", ded.size = " << deductions.size();

    if (config.nra_use_stat) { config.nra_stat.increase_assert(); }

    if (m_need_init) { initialize(m_lits); }

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
        shared_ptr<constraint> const ctr = it->second;
        m_stack.push_back(ctr);
        if (ctr->get_type() == constraint_type::Nonlinear) {
            // Try to prune box using the constraint via callign simplify
            lbool const simplify_result = simplify(e, e->getPolarity(), m_box);
            if (simplify_result == l_True) {
                m_used_constraint_vec.push_back(ctr);
                if (m_box.is_empty()) {
                    explanation = generate_explanation(m_used_constraint_vec);
                    return false;
                } else {
                    return true;
                }
            } else if (simplify_result == l_False) {
                m_used_constraint_vec.push_back(ctr);
            }
        }
    } else if (e->isIntegral() && e->getPolarity() == l_False) {
        return true;
    } else {
        DREAL_LOG_FATAL << "Unknown literal "
                        << (e->getPolarity() == l_False ? "!" : "")
                        << e << " is asserted";
        throw logic_error("unknown literal is asserted");
    }
    return true;
}

// Update ctr_map by adding new nonlinear_constraints
static void initialize_nonlinear_constraints(map<pair<Enode*, bool>, shared_ptr<constraint>> & ctr_map,
                                      vector<Enode *> const & lits,
                                      unordered_set<Enode *> const & var_set) {
    // Create Nonlinear constraints.
    for (Enode * const l : lits) {
        auto it_nc_pos = ctr_map.find(make_pair(l, true));
        auto it_nc_neg = ctr_map.find(make_pair(l, false));
        if (it_nc_pos == ctr_map.end()) {
            auto nc_pos = make_shared<nonlinear_constraint>(l, var_set, l_True);
            DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect NonlinearConstraint (+): " << *nc_pos;
            ctr_map.emplace(make_pair(l, true), nc_pos);
        }
        if (it_nc_neg == ctr_map.end()) {
            auto nc_neg = make_shared<nonlinear_constraint>(l, var_set, l_False);
            DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect NonlinearConstraint (-): " << *nc_neg;
            ctr_map.emplace(make_pair(l, false), nc_neg);
        }
    }
}

// Update ctr_map by adding new ode constraints, from the information collected in ints and invs
static void initialize_ode_constraints(map<pair<Enode*, bool>, shared_ptr<constraint>> & ctr_map,
                                vector<integral_constraint> const & ints,
                                vector<shared_ptr<forallt_constraint>> const & invs) {
    // Attach the corresponding forallT literals to integrals
    for (integral_constraint ic : ints) {
        vector<shared_ptr<forallt_constraint>> local_invs;
        for (shared_ptr<forallt_constraint> fc : invs) {
            // Link ForallTConstraint fc with IntegralConstraint ic, if
            //    fc.flow == ic.flow
            //    vars(fc.inv) \subseteq ic.vars_t
            if (fc->get_flow_id() == ic.get_flow_id()) {
                unordered_set<Enode *> vars_in_fc = fc->get_inv()->get_vars();
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
        shared_ptr<constraint> oc(new ode_constraint(ic, local_invs));
        DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect ODEConstraint: " << *oc;
        ctr_map.emplace(make_pair(ic.get_enode(), true), oc);
    }
}

// Given a list of theory literals (vector<Enode *>)
// build a mapping from Enode to constraint (m_ctr_map)
void nra_solver::initialize_constraints(vector<Enode *> const & lits) {
    vector<integral_constraint> ints;
    vector<shared_ptr<forallt_constraint>> invs;
    vector<Enode *> nonlinear_lits;
    unordered_set<Enode *> var_set;
    for (Enode * l : lits) {
        // collect var_set
        unordered_set<Enode *> const & vars = l->get_exist_vars();
        var_set.insert(vars.begin(), vars.end());
    }
    for (Enode * l : lits) {
        // Partition ODE-related constraint into integrals and forallTs
        if (l->isIntegral()) {
            integral_constraint ic = mk_integral_constraint(l, egraph.flow_maps);
            ints.push_back(ic);
        } else if (l->isForall()) {
            // Collect Generic Forall constraints.
            auto it_fc_pos = m_ctr_map.find(make_pair(l, true));
            auto it_fc_neg = m_ctr_map.find(make_pair(l, false));
            if (it_fc_pos == m_ctr_map.end()) {
                shared_ptr<constraint> fc_pos(new generic_forall_constraint(l, l_True));
                DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect GenericForallConstraint (+): " << *fc_pos;
                m_ctr_map.emplace(make_pair(l, true), fc_pos);
            }
            if (it_fc_neg == m_ctr_map.end()) {
                shared_ptr<constraint> fc_neg (new generic_forall_constraint(l, l_False));
                DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect GenericForallConstraint (-): " << *fc_neg;
                m_ctr_map.emplace(make_pair(l, false), fc_neg);
            }
        } else if (l->isForallT()) {
            shared_ptr<forallt_constraint> fc(new forallt_constraint(l, var_set));
            if (!l->get4th()->isTrue()) {
                invs.push_back(fc);
            }
            m_ctr_map.emplace(make_pair(l, true), fc);
            // TODO(soonhok): for now, a negation of forallt
            // constraint is the same forallt constraint, but it will
            // be ignored by contractor_capd4.
            //
            // Later, we will implement existt constraint and ODE contractors will support it
            m_ctr_map.emplace(make_pair(l, false), fc);
        } else if (l->get_forall_vars().empty()) {
            nonlinear_lits.push_back(l);
        } else {
            DREAL_LOG_FATAL << "nra_solver::initialize_constraints: No Patten";
            throw runtime_error("nra_solver::initialize_constraints: No Patten");
        }
    }
    initialize_ode_constraints(m_ctr_map, ints, invs);
    initialize_nonlinear_constraints(m_ctr_map, nonlinear_lits, var_set);
}

void nra_solver::initialize(vector<Enode *> const & lits) {
    m_box.constructFromLiterals(lits);
    initialize_constraints(lits);
    m_need_init = false;
}


// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint() {
    DREAL_LOG_INFO << "nra_solver::pushBacktrackPoint " << m_stack.size();
    if (m_need_init) { initialize(m_lits); }
    if (config.nra_use_stat) { config.nra_stat.increase_push(); }
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
    if (config.nra_use_stat) { config.nra_stat.increase_pop(); }
    DREAL_LOG_INFO << "nra_solver::popBacktrackPoint\t m_stack.size()      = " << m_stack.size();
    m_boxes.pop();
    m_box = m_boxes.last();
    m_used_constraint_vec.pop();
    m_stack.pop();
}

void nra_solver::handle_sat_case(box const & b) const {
    // SAT
    // --proof option
    if (config.nra_proof) {
        config.nra_proof_out.close();
        config.nra_proof_out.open(config.nra_proof_out_name.c_str(), ofstream::out | ofstream::trunc);
        display(config.nra_proof_out, b, !config.nra_readable_proof, true);
    }
#ifdef SUPPORT_ODE
    // --visualize option
    if (config.logic == QF_NRA_ODE && config.nra_json) {
        try {
            json traces = {};
            // Need to run ODE pruning operator once again to generate a trace
            for (shared_ptr<constraint> const ctr : m_stack) {
                if (ctr->get_type() == constraint_type::ODE) {
                    contractor_capd_full fwd_full(b, dynamic_pointer_cast<ode_constraint>(ctr), ode_direction::FWD, config.nra_ODE_taylor_order, config.nra_ODE_grid_size);
                    json trace = fwd_full.generate_trace(b, config);
                    traces.push_back(trace);
                }
            }
            json vis_json;
            vis_json["traces"] = traces;
            config.nra_json_out << vis_json.dump() << endl;;
        } catch (contractor_exception const & e) {
            DREAL_LOG_FATAL << "The following exception is generated while computing a trace (visualization)." << endl;
            DREAL_LOG_FATAL << e.what();
            DREAL_LOG_FATAL << "This indicates that this delta-sat result is not properly checked by ODE pruning operators.";
            DREAL_LOG_FATAL << "Please re-run the tool with a smaller precision (current precision = " << config.nra_precision << ")." << endl;
        }
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
                shared_ptr<constraint> ctr = it->second;
                shared_ptr<nonlinear_constraint> const nl_ctr = dynamic_pointer_cast<nonlinear_constraint>(ctr);
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
    if (config.nra_use_stat) { config.nra_stat.increase_check(complete); }
    if (m_stack.size() == 0) { return true; }
    DREAL_LOG_INFO << "nra_solver::check(complete = " << boolalpha << complete << ")"
                   << "stack size = " << m_stack.size();
    default_strategy stg;
    m_ctc = stg.build_contractor(m_box, m_stack, complete, config);
    if (complete) {
        // Complete Check ==> Run ICP
        if (config.nra_simulation_thread) {
            m_box = simulation_icp::solve(m_box, m_ctc, m_lits, config, egraph);
        } else if (config.nra_ncbt) {
            m_box = ncbt_icp::solve(m_box, m_ctc, config);
        } else if (config.nra_multiprune) {
            SizeGradAsinhBrancher sb1(m_stack);
            m_box = multiprune_icp::solve(m_box, m_ctc, config, sb1);
        } else if (config.nra_multiheuristic) {
            SizeBrancher sb;
            SizeGradAsinhBrancher sb1(m_stack);
            vector<std::reference_wrapper<BranchHeuristic>> heuristics = {sb, sb1};
            m_box = multiheuristic_icp::solve(m_box, m_ctc, config, heuristics);
        } else if (config.nra_linear_only) {
#ifdef USE_GLPK
            unordered_set<Enode *> linear_stack;
            for (auto c : m_stack) {
                assert(c->get_enodes().size() == 1);
                linear_stack.emplace(c->get_enodes()[0]);
                m_used_constraint_vec.push_back(c);
            } 
            glpk_wrapper solver(m_box, linear_stack);
            bool result = solver.is_sat();
            if (!result) {
                explanation = generate_explanation(m_used_constraint_vec);
            } else {
                handle_sat_case(m_box);
            }
            return result;
#else
            throw runtime_error("Compile dReal with USE_GLPK to use the LP+ICP solver.");
#endif
        } else if (config.nra_lp){
#ifdef USE_GLPK
            m_box = lp_icp::solve(m_box, m_ctc, m_stack, config);
#else
            throw runtime_error("Compile dReal GLPK (cmake `-DUSE_GLPK=true`) to use the LP+ICP solver.");
#endif
        } else {
            m_box = naive_icp::solve(m_box, m_ctc, config);
        }
    } else {
        // Incomplete Check ==> Prune Only
        try {
            m_ctc.prune(m_box, config);
            if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
    }
    bool result = !m_box.is_empty();
    DREAL_LOG_INFO << "nra_solver::check: result = " << boolalpha << result;
    for (shared_ptr<constraint> const ctr : m_ctc.used_constraints()) {
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

vector<Enode *> nra_solver::generate_explanation(scoped_vec<shared_ptr<constraint>> const & ctr_vec) {
    unordered_set<Enode *> bag;
    for (shared_ptr<constraint> ctr : ctr_vec) {
        vector<Enode *> const & enodes_in_ctr = ctr->get_enodes();
        for (Enode * const e : enodes_in_ctr) {
            if (e->hasPolarity()) {
                bag.insert(e);
            }
        }
    }
    vector<Enode *> exps(bag.begin(), bag.end());
    sort(exps.begin(), exps.end(), [](Enode const * const e1, Enode const * const e2) {
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
    if (m_need_init) {
        initialize(m_lits);
    }
    // --model option
    if (config.nra_model && config.nra_multiple_soln == 1) {
        // Only output here when --multiple_soln is not used
        output_solution(m_box, config);
    }
}

Enode * nra_solver::new_slack_var() {
    Snode * s = sstore.mkReal();
    int num = slack_vars.size();
    //  cout << "slack var number: "<< num << endl;
    string name("slack_var_");
    name += std::to_string(num);
    egraph.newSymbol(name.c_str(), s, true);

    Enode * var = egraph.mkVar(name.c_str());
    slack_vars.push_back(var);
/*
    var->setDomainLowerBound(lb);
    var->setDomainUpperBound(ub);
    var->setValueLowerBound(lb);
    var->setValueUpperBound(ub);
*/
    return var;
}

Enode * nra_solver::slack_term(Enode * e) {
    if (e->isConstant() || e->isNumb() || e->isVar()) {
        return e;
    } else if (e->isTerm()) {
        assert(e->getArity() >= 1);
        enodeid_t id = e->getCar()->getId();
        Enode * ret;
        Enode * tmp = e;
        switch (id) {
        case ENODE_ID_PLUS:
            ret = slack_term(tmp->get1st());
            tmp = tmp->getCdr()->getCdr();
            while (!tmp->isEnil()) {
                ret = egraph.mkPlus(ret, slack_term(tmp->getCar()));
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_MINUS:
            ret = slack_term(tmp->get1st());
            tmp = tmp->getCdr()->getCdr();
            while (!tmp->isEnil()) {
                ret = egraph.mkMinus(ret, slack_term(tmp->getCar()));
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_UMINUS:
            ret = slack_term(tmp->get1st());
            assert(tmp->getArity() == 1);
            return egraph.mkUminus(egraph.cons(ret));
        default:
            // not descending to subtrees for now
            Enode * svar = new_slack_var();
            Enode * sctr = egraph.mkEq(egraph.cons(svar, egraph.cons(e)));
            slack_ctrs.push_back(sctr);
            // slack_ctrs_tmp.push_back(sctr);
            return svar;
        }
    } else {
        throw runtime_error("Slack operation error.");
    }
}

Enode * nra_solver::slack_constraint(Enode * e) {
    assert(e->getArity() == 2);

    Enode * left = e -> get1st();
    Enode * right = e -> get2nd();
    Enode * head = e -> getCar();

    Enode * linear_left = slack_term(left);
    Enode * linear_right = slack_term(right);

    Enode * ret = egraph.cons(head, egraph.cons(linear_left, egraph.cons(linear_right)));

    return ret;
}






}  // namespace dreal
