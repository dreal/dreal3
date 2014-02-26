/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <iomanip>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include "dsolvers/icp_solver.h"
#include "dsolvers/util/logger.h"
#include "dsolvers/util/scoped_env.h"
#include "dsolvers/util/scoped_vec.h"

using std::cerr;
using std::endl;
using std::setw;
using std::stable_sort;
using std::unordered_map;
using std::unordered_set;

icp_solver::icp_solver(SMTConfig & c, Egraph & e, SStore & t, scoped_vec const & stack, scoped_env & env,
                       vector<Enode*> & exp, bool complete_check)
    : m_config(c), m_egraph(e), m_sstore(t), m_propag(nullptr), m_boxes(env.size()), m_ep(nullptr), m_sol(0),
      m_nsplit(0), m_explanation(exp), m_stack(stack), m_env(env), m_complete_check(complete_check) {
    rp_init_library();
    m_problem = create_rp_problem();
    m_propag = new rp_propagator(m_problem, 10.0, c.nra_verbose, c.nra_proof_out);
    rp_new(m_vselect, rp_selector_existence, (m_problem)); // rp_selector_existence
    rp_new(m_dsplit, rp_splitter_bisection, (m_problem)); // rp_splitter_mixed
    // Check once the satisfiability of all the constraints
    // Necessary for variable-free constraints
    bool sat = true;
    for (int i = 0; i < rp_problem_nctr(*m_problem); i++) {
        if (rp_constraint_unfeasible(rp_problem_ctr(*m_problem, i), rp_problem_box(*m_problem))) {
            sat = false;
            break;
        }
    }
    if (sat) {
        // Insertion of the initial box in the search structure
        m_boxes.insert(rp_problem_box(*m_problem));
        // Management of improvement factor
        if ((c.nra_icp_improve >= 0.0) && (c.nra_icp_improve <= 100.0)) {
            m_improve = 1.0 - c.nra_icp_improve / 100.0;
        } else {
            m_improve = 0.875; /* 12.5% */
        }
        m_propag->set_improve(m_improve);
        // Creation of the operators and insertion in the propagator
        rp_hybrid_factory hfact(m_improve);
        hfact.apply(m_problem, *m_propag);
        rp_domain_factory dfact;
        dfact.apply(m_problem, *m_propag);
        rp_newton_factory nfact(m_improve);
        nfact.apply(m_problem, *m_propag);
        // Used for round-robin strategy: last variable split
        rp_box_set_split(m_boxes.get(), -1);// sean: why is the last variable -1? oh, must be length - this number
    } else {
        rp_box_set_empty(rp_problem_box(*m_problem));
    }
#ifdef ODE_ENABLED
    if (m_complete_check && m_config.nra_contain_ODE) {
        create_ode_solvers();
    }
#endif
}

icp_solver::~icp_solver() {
    rp_delete(m_vselect);
    rp_delete(m_dsplit);
    rp_reset_library();
    delete m_propag;
    for (rp_variable * v : m_rp_variables)     { delete v; }
    for (rp_constraint * c : m_rp_constraints) { delete c; }
#ifdef ODE_ENABLED
    for (ode_solver * s : m_ode_solvers)       { delete s; }
#endif
    rp_problem_destroy(m_problem);
    delete m_problem;
}

#ifdef ODE_ENABLED
void icp_solver::create_ode_solvers() {
    // collect intergral and vector literals
    vector<Enode*> vec_integral;
    vector<Enode*> vec_inv;
    for (auto const l : m_stack) {
        // ignore if the polarity is "false".
        if (l->isIntegral() && l->getPolarity().toInt()) {
            vec_integral.push_back(l);
        } else if (l->isForallT() && l->getPolarity().toInt()) {
            vec_inv.push_back(l);
        }
    }

    // For each intergral literal, we create an ODE solver.
    // We need to collect all the relevent invariants to an intergral
    // literal. To do so, we check whether there exists any
    // overlapping between variables in an intergral literal and
    // invariant literral.
    for (auto const l_int : vec_integral) {
        vector<Enode*> invs;
        for (auto const l_inv : vec_inv) {
            unordered_set<Enode *> vars_int = l_int->get_vars();
            unordered_set<Enode *> vars_inv = l_inv->get_vars();
            bool intersect = any_of(vars_int.begin(), vars_int.end(), [&vars_inv](Enode * v_int) {
                    return find(vars_inv.begin(), vars_inv.end(), v_int) != vars_inv.end();
                });
            if (intersect) {
                invs.push_back(l_inv);
            }
        }
        m_ode_solvers.push_back(new ode_solver(m_config, m_egraph, l_int, invs, m_enode_to_rp_id));
    }
}
#endif

rp_problem* icp_solver::create_rp_problem() {
    rp_problem* rp_prob = new rp_problem;
    rp_problem_create(rp_prob, "icp_holder");

    // ======================================
    // Create rp_variable for each var in env
    // ======================================
    for (auto const & p : m_env) {
        Enode* const key = p.first;
        double const lb = p.second.first;
        double const ub = p.second.second;

        rp_variable * v = new rp_variable;
        m_rp_variables.push_back(v);
        string name = key->getCar()->getName();
        rp_variable_create(v, name.c_str());
        int rp_id = rp_vector_insert(rp_table_symbol_vars(rp_problem_symb(*rp_prob)), *v);
        rp_box_enlarge_size(&rp_problem_box(*rp_prob), 1);
        rp_bsup(rp_box_elem(rp_problem_box(*rp_prob), rp_id)) = ub;
        rp_binf(rp_box_elem(rp_problem_box(*rp_prob), rp_id)) = lb;
        rp_union_interval u;
        rp_union_create(&u);
        rp_union_insert(u, rp_box_elem(rp_problem_box(*rp_prob), rp_id));
        rp_union_copy(rp_variable_domain(*v), u);
        rp_union_destroy(&u);

        rp_variable_set_real(*v);
        rp_variable_precision(*v) = m_config.nra_precision;
        m_enode_to_rp_id[key] = rp_id;
        DREAL_LOG_DEBUG("Key: " << name << "\t" << "value : [" << lb << ", " << ub << "] \t" << "precision : " << m_config.nra_precision << "\t" << "rp_id: " << rp_id);
    }

    // ===============================================
    // Create rp_constraints for each literal in stack
    // ===============================================
    for (auto const l : m_stack) {
        // Do not create rp_constraints for ForallT and Integral
        if (l->isForallT() || l->isIntegral()) {
            continue;
        }
        stringstream buf;
        rp_constraint * c = new rp_constraint;
        m_rp_constraints.push_back(c);
        l->print_infix(buf, l->getPolarity());
        string constraint_str = buf.str();
        if (constraint_str.compare("0 = 0") != 0) {
            DREAL_LOG_DEBUG("Constraint: " << (l->getPolarity() == l_True ? " " : "Not") << l);
            DREAL_LOG_DEBUG(" : " << constraint_str);
            // Parse the string (infix form) to create the constraint c
            rp_parse_constraint_string(c, constraint_str.c_str(), rp_problem_symb(*rp_prob));
            // Add to the problem
            rp_vector_insert(rp_problem_ctrs(*rp_prob), *c);
            // Update Counter
            for (int i = 0; i <rp_constraint_arity(*c); ++i) {
                ++rp_variable_constrained(rp_problem_var(*rp_prob, rp_constraint_var(*c, i)));
            }
        }
    }
    return rp_prob;
}

#ifdef ODE_ENABLED
void icp_solver::callODESolver(ode_solver * odeSolver, bool forward, bool & ODE_result, bool & have_exception) {
    ODE_result = true;
    have_exception = false;

    // Simple ODE
    ODE_result = odeSolver->simple_ODE(m_boxes.get(), forward) &&
        m_propag->apply(m_boxes.get());
    if (!ODE_result) {
        return;
    }

    // First Try (Forward or Backward).
    try {
        if (forward) {
            ODE_result = odeSolver->solve_forward(m_boxes.get())
                && m_propag->apply(m_boxes.get());
        } else {
            ODE_result = odeSolver->solve_backward(m_boxes.get())
                && m_propag->apply(m_boxes.get());
        }
    }
    catch(exception& e) {
        DREAL_LOG_INFO("Exception in ODE Solving " << (forward ? "(Forward)" : "(Backward)"));
        DREAL_LOG_INFO(e.what());
        have_exception = true;
    }
    if (!ODE_result) {
        return;
    }

    // Second Try (Backward or Forward).
    try {
        if (forward) {
            ODE_result = odeSolver->solve_backward(m_boxes.get())
                && m_propag->apply(m_boxes.get());
        } else {
            ODE_result = odeSolver->solve_forward(m_boxes.get())
                && m_propag->apply(m_boxes.get());
        }
    }
    catch(exception& e) {
        DREAL_LOG_INFO("Exception in ODE Solving " << (forward ? "(Forward)" : "(Backward)"));
        DREAL_LOG_INFO(e.what());
        have_exception = true;
    }
    return;
}
#endif

// Update the lower and upperbound of Enode e and its corresponding
// rp_variable using the given parameters lb and ub.
//
//    [e.lb, e.ub] = [e.lb, e.ub] /\ [lb, ub]
//
// Return false if the result is empty interval
//        true  o.w.
//
bool icp_solver::updateValue(Enode * e, double lb, double ub) {
    rp_box b = m_boxes.get();
    DREAL_LOG_DEBUG("UpdateValue : " << e
                    << " ["      << rp_binf(rp_box_elem(b, m_enode_to_rp_id[e]))
                    << ", "      << rp_bsup(rp_box_elem(b, m_enode_to_rp_id[e]))
                    << "] /\\ [" << lb << ", " << ub << "]");
    double new_lb = max(lb, rp_binf(rp_box_elem(b, m_enode_to_rp_id[e])));
    double new_ub = min(ub, rp_bsup(rp_box_elem(b, m_enode_to_rp_id[e])));
    if (new_lb <= new_ub) {
        e->setLowerBound(new_lb);
        rp_binf(rp_box_elem(b, m_enode_to_rp_id[e])) = new_lb;
        e->setUpperBound(new_ub);
        rp_bsup(rp_box_elem(b, m_enode_to_rp_id[e])) = new_ub;
        DREAL_LOG_DEBUG(" = [" << new_lb << ", " << new_ub << "]");
        return true;
    } else {
        rp_interval_set_empty(rp_box_elem(b, m_enode_to_rp_id[e]));
        e->setLowerBound(+numeric_limits<double>::infinity());
        e->setUpperBound(-numeric_limits<double>::infinity());
        DREAL_LOG_DEBUG(" = empty ");
        return false;
    }
}

void print_interval(ostream & out, double lb, double ub) {
    out << "[" << lb << ", " << ub << "]";
}

void display_cache_entry(vector<double> const & e, Enode * time_var, vector<Enode *> const & vars) {
    auto it = e.cbegin();
    cerr << "Mode: " << *(it++) << endl;
    cerr << setw(15) << time_var << " : ";
    double time_lb = *(it++);
    double time_ub = *(it++);
    print_interval(cerr, time_lb, time_ub);
    cerr << endl;
    for (Enode * var : vars) {
        double lb = *(it++);
        double ub = *(it++);
        cerr << setw(15) << var << " : ";
        print_interval(cerr, lb, ub);
        cerr << endl;
    }
}

bool icp_solver::prop_with_ODE() {
    if (m_propag->apply(m_boxes.get())) {
#ifdef ODE_ENABLED
        if (m_config.nra_contain_ODE) {
            // Sort ODE Solvers by their logVolume.
            sort(m_ode_solvers.begin(), m_ode_solvers.end(),
                 [this](ode_solver * odeSolver1, ode_solver * odeSolver2) {
                     rp_box b = m_boxes.get();
                     double const min1 = min(odeSolver1->logVolume_X0(b), odeSolver1->logVolume_Xt(b));
                     double const min2 = min(odeSolver2->logVolume_X0(b), odeSolver2->logVolume_Xt(b));
                     return min1 < min2;
                 });
            for (auto const & odeSolver : m_ode_solvers) {
                rp_box b = m_boxes.get();
                double const lv_x0 = odeSolver->logVolume_X0(b);
                double const lv_xt = odeSolver->logVolume_Xt(b);
                unsigned const mode = odeSolver->getMode();
                bool forward = m_config.nra_ODE_forward_only ? true : lv_x0 <= lv_xt;
                DREAL_LOG_DEBUG(setw(10) << mode << setw(20) << lv_x0 << setw(20) << lv_xt
                               << setw(20) << (forward ? "Forward" : "Backward"));
                if (!m_config.nra_ODE_cache) {
                    bool result = true, have_exception = false;
                    callODESolver(odeSolver, forward, result, have_exception);
                    if (!result) {
                        return false;
                    }
                } else {
                    static map<vector<double>, tuple<bool, bool, vector<double>>> cache_X0;
                    static map<vector<double>, tuple<bool, bool, vector<double>>> cache_Xt;
                    static unsigned hit = 0;
                    static unsigned nohit = 0;
                    static unsigned expt = 0;
                    DREAL_LOG_DEBUG(" HIT : " << setw(10) << hit << " NOHIT  : " << setw(10) << nohit
                                   << " EXCEPT : " << setw(10) << expt);
                    if (forward) {
                        // Forward Pruning
                        vector<double> currentX0T = odeSolver->extractX0T(b);
                        auto it = cache_X0.find(currentX0T);
                        if (it != cache_X0.end()) {
                            // Cache is HIT!
                            hit++;
                            bool cached_result    = get<0>(it->second);
                            bool cached_exception = get<1>(it->second);
                            if (!cached_result) {
                                return false;
                            }
                            if (cached_exception)
                                continue;
                            vector<double> const & cached_info = get<2>(it->second);

                            // use cached time
                            Enode * time = odeSolver->get_Time();
                            double cached_time_lb = cached_info[1];
                            double cached_time_ub = cached_info[2];
                            bool result = updateValue(time, cached_time_lb, cached_time_ub);
                            if (!result) {
                                return false;
                            }
                            // use cached X_t
                            // note: cached_info[3] is the beginning of X_t info
                            unsigned i = 3;
                            for (Enode * var : odeSolver->get_Xt()) {
                                double cached_var_lb = cached_info[i++];
                                double cached_var_ub = cached_info[i++];
                                result = updateValue(var, cached_var_lb, cached_var_ub);
                                if (!result) {
                                    return false;
                                }
                            }
                        } else {
                            nohit++;
                            // Cache is Miss! Call ODE Solver and save the result
                            bool result = true;
                            bool have_exception = false;
                            callODESolver(odeSolver, forward, result, have_exception);
                            if (!have_exception) {
                                cache_X0.emplace(currentX0T, make_tuple(result, have_exception, odeSolver->extractXtT(m_boxes.get())));
                            } else {
                                // cache_X0.emplace(currentX0T, make_tuple(result, have_exception, odeSolver->extractXtT(m_boxes.get())));
                                expt++;
                            }
                            if (!result) {
                                return false;
                            }
                        }
                    } else {
                        // Backward Pruning
                        vector<double> currentXtT = odeSolver->extractXtT(b);
                        auto it = cache_Xt.find(currentXtT);
                        if (it != cache_Xt.end()) {
                            // Cache is HIT!
                            hit++;
                            bool cached_result    = get<0>(it->second);
                            bool cached_exception = get<1>(it->second);
                            if (!cached_result)
                                return false;
                            if (cached_exception)
                                continue;
                            vector<double> const & cached_info = get<2>(it->second);

                            // use cached time
                            Enode * time = odeSolver->get_Time();
                            double cached_time_lb = cached_info[1];
                            double cached_time_ub = cached_info[2];
                            bool result = updateValue(time, cached_time_lb, cached_time_ub);
                            if (!result)
                                return false;
                            // use cached X_0
                            // note: cached_info[3] is the beginning of X_0 info
                            unsigned i = 3;
                            for (Enode * var : odeSolver->get_X0()) {
                                double cached_var_lb = cached_info[i++];
                                double cached_var_ub = cached_info[i++];
                                result = updateValue(var, cached_var_lb, cached_var_ub);
                                if (!result)
                                    return false;
                            }
                        } else {
                            // Cache is Miss! Call ODE Solver and save the result
                            nohit++;
                            bool result = true;
                            bool have_exception = false;
                            callODESolver(odeSolver, forward, result, have_exception);
                            if (!have_exception) {
                                cache_Xt.emplace(currentXtT, make_tuple(result, have_exception, odeSolver->extractX0T(m_boxes.get())));
                            } else {
                                // cache_Xt.emplace(currentXtT, make_tuple(result, have_exception, odeSolver->extractX0T(m_boxes.get())));
                                expt++;
                            }
                            if (!result)
                                return false;
                        }
                    }
                }
            }
        }
        return true;
#endif
        return true;
    }
    return false;
}

rp_box icp_solver::compute_next() {
    if (m_sol > 0) { m_boxes.remove(); }
    while (!m_boxes.empty()) {
        if (prop_with_ODE()) { // sean: here it is! propagation before split!!!
            // SAT => Split
            rp_box b = m_boxes.get();
            int i = m_vselect->apply(b);
            if (i >= 0 && rp_box_width(b) >= m_config.nra_precision) {
                if (m_config.nra_proof) {
                    m_config.nra_proof_out << endl
                                           << "[branched on "
                                           << rp_variable_name(rp_problem_var(*m_problem, i))
                                           << "]"
                                           << endl;
                    pprint_vars(m_config.nra_proof_out, *m_problem, b);
                }
                ++m_nsplit;
                m_dsplit->apply(m_boxes, i);
            } else {
                ++m_sol;
                if (m_ep) m_ep->prove(b);
                return(b);
            }
        } else {
            // UNSAT => Remove box
            if (m_config.nra_proof) { m_config.nra_proof_out << "[conflict detected]" << endl; }
            m_boxes.remove();
        }
    }
    return nullptr;
}


#ifdef ODE_ENABLED
void icp_solver::print_ODE_trajectory(ostream& out) const {
    if (m_ode_solvers.size() == 0)
        return;
    bool first_one = true;
    for (auto const & ode_solver : m_ode_solvers) {
        if (ode_solver != nullptr) {
            if (first_one) {
                first_one = false;
            } else {
                out << "," << endl;
            }
            ode_solver->print_trajectory(out);
        }
    }
}
#endif

bool icp_solver::solve() {
    if (m_config.nra_proof) { output_problem(); }
    if (rp_box_empty(rp_problem_box(*m_problem))) {
        DREAL_LOG_DEBUG("Unfeasibility detected before solving");
        m_explanation.clear();
        copy(m_stack.cbegin(), m_stack.cend(), back_inserter(m_explanation));
        return false;
    } else {
        rp_box b = compute_next();
        if (b != nullptr) {
            /* SAT */
            DREAL_LOG_DEBUG("SAT with the following box:");
            if (m_config.nra_verbose) { pprint_vars(cerr, *m_problem, b); }
            if (m_config.nra_proof) {
                m_config.nra_proof_out.close();
                m_config.nra_proof_out.open(m_config.nra_proof_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
                m_config.nra_proof_out << "SAT with the following box:" << endl;
                pprint_vars(m_config.nra_proof_out, *m_problem, b);
                m_config.nra_proof_out << endl;
            }
            return true;
        } else {
            /* UNSAT */
            DREAL_LOG_DEBUG("UNSAT!");
            m_explanation.clear();
            copy(m_stack.cbegin(), m_stack.cend(), back_inserter(m_explanation));
            return false;
        }
    }
}

void icp_solver::display_box(ostream& out, rp_box b, int digits, int mode) const {
    if (rp_box_empty(b)) {
        out << "empty";
    } else {
        out << "(";
        for (int i = 0; i < rp_box_size(b); ++i) {
            display_interval(out, rp_box_elem(b, i), digits, mode);
            if (i < (rp_box_size(b) - 1)) {
                out << ",";
            }
        }
        out << ")";
    }
}

void icp_solver::display_interval(ostream & out, rp_interval i, int digits, int mode) const {
    if (rp_interval_empty(i)) {
        out << "empty";
        return;
    }
    if (rp_interval_point(i) == true) {
        if (rp_binf(i) >= 0) {
            out.precision(digits);
            out << rp_binf(i);
        } else {
            out.precision(digits);
            out << rp_binf(i);
        }
    } else {
        if (mode == RP_INTERVAL_MODE_BOUND) {
            if (rp_binf(i) >= 0) {
                if (rp_binf(i) == 0) {
                    out << "[0" << RP_INTERVAL_SEPARATOR;
                } else {
                    RP_ROUND_DOWNWARD();
                    out.precision(digits);
                    out << "[" << rp_binf(i) << RP_INTERVAL_SEPARATOR;
                }
                RP_ROUND_UPWARD();
                if (rp_bsup(i) == RP_INFINITY) {
                    out << "+oo";
                } else {
                    out.precision(digits);
                    out << rp_bsup(i) << "]";
                }
            } else {
                RP_ROUND_DOWNWARD();
                if (rp_binf(i) == -RP_INFINITY) {
                    out << "(-oo" << RP_INTERVAL_SEPARATOR;
                } else {
                    out.precision(digits);
                    out << "[" << rp_binf(i) << RP_INTERVAL_SEPARATOR;
                }
                RP_ROUND_UPWARD();
                if (rp_bsup(i) == RP_INFINITY) {
                    out << "+oo";
                } else {
                    if (rp_bsup(i) == 0) {
                        out << "0]";
                    } else {
                        out.precision(digits);
                        out << rp_bsup(i) << "]";
                    }
                }
            }
        }
    }
}

void icp_solver::pprint_vars(ostream & out, rp_problem p, rp_box b) const {
    for (int i = 0; i <rp_problem_nvar(p); i++) {
        out << setw(15);
        out << rp_variable_name(rp_problem_var(p, i));
        out << " : ";
        display_interval(out, rp_box_elem(b, i), 16, RP_INTERVAL_MODE_BOUND);
        if (i != rp_problem_nvar(p) - 1)
            out << ";";
        out << endl;
    }
}

void icp_solver::output_problem() const {
    m_config.nra_proof_out.precision(16);
    m_config.nra_proof_out << "Precision:" << m_config.nra_precision << endl;

    // Print out all the Enode in stack
    for (auto const l : m_stack) {
        if (l->getPolarity() == l_True) {
            m_config.nra_proof_out << l << endl;
        } else if (l->getPolarity() == l_False) {
            if (l->isEq()) {
                /* PRINT NOTHING */
            } else {
                m_config.nra_proof_out << "(not " << l << ")" << endl;
            }
        } else {
            assert(0);
        }
    }

    // Print out the initial values
    for (auto const & p : m_env) {
        Enode* const key = p.first;
        double const lb = p.second.first;
        double const ub = p.second.second;

        m_config.nra_proof_out << key << ": ";
        if (lb == -numeric_limits<double>::infinity()) {
            m_config.nra_proof_out << "(-oo";
        } else {
            m_config.nra_proof_out.precision(16);
            m_config.nra_proof_out << "[" << lb;
        }
        m_config.nra_proof_out << ", ";
        if (ub == numeric_limits<double>::infinity()) {
            m_config.nra_proof_out << "+oo)";
        } else {
            m_config.nra_proof_out.precision(16);
            m_config.nra_proof_out << ub << "]";
        }
        m_config.nra_proof_out << ";" << endl;
    }
}

// return true if the box is non-empty after propagation
// false if the box is *empty* after propagation
bool icp_solver::prop() {
    bool result = false;
    if (m_config.nra_proof) { output_problem(); }
    if (m_sol > 0) { m_boxes.remove(); }
    if (!m_boxes.empty()) { result = m_propag->apply(m_boxes.get()); }
    if (!result) {
        // UNSAT
        if (m_config.nra_proof) { m_config.nra_proof_out << "[conflict detected]" << endl; }
        m_explanation.clear();
        copy(m_stack.cbegin(), m_stack.cend(), back_inserter(m_explanation));
    } else {
        // SAT, Update Env
        rp_box const b = m_boxes.get();
        for (auto const & p : m_env) {
            Enode* const key = p.first;
            int const rp_id = m_enode_to_rp_id[key];
            m_env.update(key, make_pair(rp_binf(rp_box_elem(b, rp_id)),
                                        rp_bsup(rp_box_elem(b, rp_id))));
        }
        if (m_config.nra_proof) { m_config.nra_proof_out << "HOLE" << endl; }
    }
    return result;
}

#ifdef ODE_ENABLED
void icp_solver::print_json(ostream & out) {
    // Print out ODE trajectory
    out << "{\"traces\": " << endl
        << "[" << endl;
    print_ODE_trajectory(out);
    out << "]" << endl << "}" << endl;
}
#endif
