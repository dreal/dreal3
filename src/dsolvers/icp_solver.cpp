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
#include <boost/algorithm/string/predicate.hpp>
#include <boost/log/core.hpp>
#include <boost/log/trivial.hpp>
#include "dsolvers/icp_solver.h"
#include "dsolvers/util/scoped_env.h"
#include "dsolvers/util/scoped_vec.h"

using boost::starts_with;
using std::cerr;
using std::endl;
using std::setw;
using std::stable_sort;
using std::unordered_map;
using std::unordered_set;

icp_solver::icp_solver(SMTConfig & c, scoped_vec const & stack, scoped_env & env,
                       vector<Enode*> & exp, unordered_map<Enode*, unordered_set<Enode*>> & odevars_in_lit,
                       bool complete_check)
    : m_config(c), m_propag(nullptr), m_boxes(env.size()), m_ep(nullptr), m_sol(0),
      m_nsplit(0), m_explanation(exp), m_stack(stack), m_env(env), m_num_ode_sgroups(1),
      m_odevars_in_lit(odevars_in_lit), m_diff_vec(1), m_complete_check(complete_check) {
    rp_init_library();
    m_problem = create_rp_problem();
    m_propag = new rp_propagator(m_problem, 10.0, c.nra_verbose, c.nra_proof_out);
    rp_new(m_vselect, rp_selector_existence, (m_problem)); // rp_selector_roundrobin
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
    // Construct m_diff_vec
    for (auto const l : m_stack) {
        unordered_set<Enode*> ode_vars = m_odevars_in_lit[l];
        for (auto const v : ode_vars) {
            unsigned const diff_sgroup = v->getODEsgroup();
            BOOST_LOG_TRIVIAL(debug) << "ode_var: " << v;
            BOOST_LOG_TRIVIAL(debug) << "diff_sgroup: " << diff_sgroup << ", num_ode_sgroups: " << m_num_ode_sgroups;
            if (diff_sgroup >= m_num_ode_sgroups) {
                m_diff_vec.resize(diff_sgroup + 1);
                m_num_ode_sgroups = diff_sgroup;
                BOOST_LOG_TRIVIAL(debug) << "diff_sgroup: " << diff_sgroup << " we do resize";
                BOOST_LOG_TRIVIAL(debug) << "num_ode_sgroups: " << m_num_ode_sgroups;
            }
            if (m_diff_vec[diff_sgroup].empty()) {
                BOOST_LOG_TRIVIAL(debug) << "diff_vec[" << diff_sgroup << "] is empty.";
            }
            m_diff_vec[diff_sgroup].insert(v);
            BOOST_LOG_TRIVIAL(debug) << "diff_sgroup inserted: " << diff_sgroup;
        }
    }
    // Construct m_ode_solvers
    m_ode_solvers.resize(m_num_ode_sgroups + 1);
    for (unsigned sg = 1; sg <= m_num_ode_sgroups; sg++) {
        if (!m_diff_vec[sg].empty()) {
            unsigned const g  = (*m_diff_vec[sg].begin())->getODEgroup();
            m_ode_solvers[sg] = new ode_solver(g, sg, m_config, m_diff_vec[sg], m_enode_to_rp_id);
            m_ode_worklist.insert(sg);
        }
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

        // rp_variable_set_real(*v);
        // rp_variable_precision(*v) = m_config.nra_precision;
        m_enode_to_rp_id[key] = rp_id;
        m_rp_id_to_enode[rp_id] = key;
        BOOST_LOG_TRIVIAL(debug) << "Key: " << name << "\t"
                                 << "value : [" << lb << ", " << ub << "] \t"
                                 << "precision : " << m_config.nra_precision << "\t"
                                 << "rp_id: " << rp_id;
    }

    // ===============================================
    // Create rp_constraints for each literal in stack
    // ===============================================
    for (auto const l : m_stack) {
        stringstream buf;
        rp_constraint * c = new rp_constraint;
        m_rp_constraints.push_back(c);
        l->print_infix(buf, l->getPolarity());
        string constraint_str = buf.str();
        if (constraint_str.compare("0 = 0") != 0) {
            BOOST_LOG_TRIVIAL(debug) << "Constraint: "
                                     << (l->getPolarity() == l_True ? " " : "Not")
                                     << l;
            BOOST_LOG_TRIVIAL(debug) << " : " << constraint_str;
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
bool icp_solver::callODESolver(int group, unordered_set<Enode*> const & ode_vars, bool forward) {
    BOOST_LOG_TRIVIAL(debug) << "solve ode group: " << group;

    // The size of ODE_Vars should be even
    if (ode_vars.size() % 2 == 1) {
        BOOST_LOG_TRIVIAL(debug) << "The size of ODE_Vars should be even";
        for (auto const ode_var : ode_vars) {
            BOOST_LOG_TRIVIAL(debug) << ode_var;
        }
        return false;
    }

    // If the _0 and _t variables do not match, return false.
    for (auto const v : ode_vars) {
        if (ode_vars.find(v->getODEopposite()) == ode_vars.end()) {
            BOOST_LOG_TRIVIAL(debug) << "the _0 and _t variables do not match:" << v;
            return false;
        }
    }

    if (!ode_vars.empty()) {
        BOOST_LOG_TRIVIAL(debug) << "Inside of current ODEs";
        for (auto const ode_var : ode_vars) {
            BOOST_LOG_TRIVIAL(debug) << "Name: " << ode_var->getCar()->getName();
        }
        ode_solver* odeSolver = m_ode_solvers[group];

        if (forward) {
            bool simple_ODE = odeSolver->simple_ODE(m_boxes.get()) && m_propag->apply(m_boxes.get());
            if (!simple_ODE) return false;

            bool forward_ODE = true;
            bool forward_exception = false;
            try {
                forward_ODE = odeSolver->solve_forward(m_boxes.get()) && m_propag->apply(m_boxes.get());
            }
            catch(exception& e) {
                BOOST_LOG_TRIVIAL(debug) << "Exception in ODE Solving (Forward)";
                BOOST_LOG_TRIVIAL(debug) << e.what();
                forward_exception = true;
            }
            if (!forward_exception) return forward_ODE;
            try {
                return odeSolver->solve_backward(m_boxes.get()) && m_propag->apply(m_boxes.get());
            }
            catch(exception& e) {
                BOOST_LOG_TRIVIAL(debug) << "Exception in ODE Solving (Backward)";
                BOOST_LOG_TRIVIAL(debug)<< e.what();
                return true;
            }
        } else {
            bool simple_ODE = odeSolver->simple_ODE(m_boxes.get()) && m_propag->apply(m_boxes.get());
            if (!simple_ODE) return false;

            bool backward_ODE = true;
            bool backward_exception = false;
            try {
                backward_ODE = odeSolver->solve_backward(m_boxes.get()) && m_propag->apply(m_boxes.get());
            }
            catch(exception& e) {
                BOOST_LOG_TRIVIAL(debug) << "Exception in ODE Solving (Backward)";
                BOOST_LOG_TRIVIAL(debug) << e.what();
                backward_exception = true;
            }
            if (!backward_exception) return backward_ODE;
            try {
                return odeSolver->solve_forward(m_boxes.get()) && m_propag->apply(m_boxes.get());
            }
            catch(exception& e) {
                BOOST_LOG_TRIVIAL(debug) << "Exception in ODE Solving (Forward)";
                BOOST_LOG_TRIVIAL(debug) << e.what();
                return true;
            }
        }
    }
    return true;
}
#endif

bool icp_solver::is_atomic(unordered_set<Enode*> const & ode_vars, double const p) {
    rp_box b = m_boxes.get();
    for (auto const ode_var : ode_vars) {
        double lb = rp_binf(rp_box_elem(b, m_enode_to_rp_id[ode_var]));
        double ub = rp_bsup(rp_box_elem(b, m_enode_to_rp_id[ode_var]));
        if (ub - lb > p) {
            return false;
        }
    }
    return true;
}

vector<pair<double, double>> icp_solver::measure_size(unordered_set<Enode*> const & ode_vars, double const prec) {
    rp_box const & b = m_boxes.get();
    vector<pair<Enode*, Enode*>> ode_pairs;

    // extract ode pairs
    for (auto const ode_var : ode_vars) {
        lbool const & odeType = ode_var->getODEvartype();
        if (odeType == l_False) {
            ode_pairs.push_back(make_pair(ode_var, ode_var->getODEopposite()));
        }
    }
    // sort ode_pairs by their rp_id
    stable_sort(ode_pairs.begin(),
         ode_pairs.end(),
         [this](pair<Enode*, Enode*> const & p1, pair<Enode*, Enode*> const & p2) {
             return m_enode_to_rp_id[p1.first] < m_enode_to_rp_id[p2.first];
         });

    // extract width
    vector<pair<double, double>> ret;
    for (auto const & p : ode_pairs) {
        double const lb_0 = rp_binf(rp_box_elem(b, m_enode_to_rp_id[p.first]));
        double const ub_0 = rp_bsup(rp_box_elem(b, m_enode_to_rp_id[p.first]));
        double const s_0 = max(ub_0 - lb_0, prec);
        double const lb_t = rp_binf(rp_box_elem(b, m_enode_to_rp_id[p.second]));
        double const ub_t = rp_bsup(rp_box_elem(b, m_enode_to_rp_id[p.second]));
        double const s_t = max(ub_t - lb_t, prec);
        ret.push_back(make_pair(s_0, s_t));
    }
    return ret;
}

bool icp_solver::prop_with_ODE() {
    if (m_propag->apply(m_boxes.get())) {
        rp_box curr_box = m_boxes.get();
        rp_box old_box;
        rp_box_create(&old_box, rp_box_size(curr_box));
        rp_box_copy(old_box, curr_box);

        double old_volume = rp_box_volume_log(old_box);
        double new_volume = old_volume;
#ifdef ODE_ENABLED
        if (m_config.nra_contain_ODE) {
            do {
                // Find ODE groups whose X_0, X_t, and T are smallest interval boxes
                vector<pair<unsigned, pair<double, double>>> ode_group_scores;
                for (unsigned i = 1; i <= m_num_ode_sgroups; i++) {
                    if (m_ode_worklist.count(i) > 0 && !m_diff_vec[i].empty()) {
                        ode_group_scores.push_back(make_pair(i, make_pair(0.0, 0.0)));
                    }
                }

                auto ratio_comp = [](pair<double, double> const & x, pair<double, double> const & y) {
                    double const x_0 = x.first;
                    double const x_t = x.second;
                    double const x_r = x_t > x_0 ? x_t / x_0 : x_0 / x_t;
                    double const y_0 = y.first;
                    double const y_t = y.second;
                    double const y_r = y_t > y_0 ? y_t / y_0 : y_0 / y_t;
                    return x_r < y_r;
                };

                auto diff_comp = [](pair<double, double> const & x, pair<double, double> const & y) {
                    double const x_0 = x.first;
                    double const x_t = x.second;
                    double const x_r = x_t > x_0 ? x_t - x_0 : x_0 - x_t;
                    double const y_0 = y.first;
                    double const y_t = y.second;
                    double const y_r = y_t > y_0 ? y_t - y_0 : y_0 - y_t;
                    return x_r < y_r;
                };

                // auto compute_max_width = [this, &ratio_comp](unordered_set<Enode*> const & vars, double const prec) {
                //     vector<pair<double, double>> s = measure_size(vars, prec);
                //     return *max_element(s.begin(), s.end(), ratio_comp);
                // };

                auto compute_volume = [this](unordered_set<Enode*> const & vars, double const prec) {
                    vector<pair<double, double>> s = measure_size(vars, prec);
                    double V_0 = 0.0;
                    double V_t = 0.0;
                    for (auto p : s) {
                        V_0 += log(std::max(prec, p.first));
                        V_t += log(std::max(prec, p.second));
                    }
                    return make_pair(V_0, V_t);
                };

                while (ode_group_scores.size() > 0 && !m_ode_worklist.empty()) {
                    // update scores
                    for (auto & t : ode_group_scores) {
                        unsigned i = t.first;
                        // auto r = compute_max_width(diff_vec[i], m_config.nra_precision);
                        auto r = compute_volume(m_diff_vec[i], m_config.nra_precision);
                        t = make_pair(i, r);
                    }
                    // Sort
                    stable_sort(ode_group_scores.begin(), ode_group_scores.end(),
                                [&ratio_comp, &diff_comp](pair<unsigned, pair<double, double>> const & x,
                                                          pair<unsigned, pair<double, double>> const & y) {
                                    auto const & p1 = x.second;
                                    auto const & p2 = y.second;
                                    return !diff_comp(p1, p2);
                                    // return false;
                                });

                    // Process first n ode groups in parallel
                    auto ite = ode_group_scores.begin();
                    unsigned num_core = 1; // std::thread::hardware_concurrency()
                    for (unsigned id = 0;
                         id < num_core && ite != ode_group_scores.end();
                         id++, ite++) {
                        auto const & t = *ite;
                        unsigned const i = t.first;
                        m_ode_worklist.erase(i);
                        if (is_atomic(m_diff_vec[i], m_config.nra_precision)) {
                            cerr << "A" << i << endl;
                            if (callODESolver(i, m_diff_vec[i], true) == false) {
                                m_ode_worklist.insert(i);
                                return false;
                            }
                        } else {
                            double const T_0_size = t.second.first;
                            double const T_x_size = t.second.second;
                            bool ode_direction = T_x_size >= T_0_size;
                            cerr << setw(20) << i << setw(20) << T_0_size << setw(20)
                                 << T_x_size << setw(20) << (ode_direction ? "Forward" : "Backward") << endl;

                            if (callODESolver(i, m_diff_vec[i], ode_direction) == false) {
                                cerr << endl;
                                m_ode_worklist.insert(i);
                                return false;
                            }
                        }
                    }
                    // Delete first one
                    ode_group_scores.erase(ode_group_scores.begin(), ite);
                }
                cerr << endl;
                if (!m_propag->apply(m_boxes.get()))
                    return false;
                old_volume = new_volume;
                rp_box curr_box = m_boxes.get();
                new_volume = rp_box_volume_log(curr_box);

                unsigned box_size = rp_box_size(curr_box);
                for (unsigned i = 0; i < box_size; i++) {
                    if (!rp_interval_equal(rp_box_elem(old_box, i), rp_box_elem(curr_box, i))) {
                        Enode * const e = m_rp_id_to_enode[i];
                        unsigned g = e->getODEgroup();
                        m_ode_worklist.insert(g);
                        cerr << e << " : " << g << " is added to worklist" << endl;
                    }
                }
                rp_box_copy(old_box, curr_box);
            } while (new_volume - old_volume <= -0.10);
            return true;
        } else {
            return true;
        }
#endif
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
                Enode * const e = m_rp_id_to_enode[i];
                m_ode_worklist.insert(e->getODEgroup());
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
        BOOST_LOG_TRIVIAL(debug) << "Unfeasibility detected before solving";
        m_explanation.clear();
        copy(m_stack.cbegin(), m_stack.cend(), back_inserter(m_explanation));
        return false;
    } else {
        rp_box b = compute_next();
        if (b != nullptr) {
            /* SAT */
            BOOST_LOG_TRIVIAL(debug) << "SAT with the following box:";
            if (m_config.nra_verbose) { pprint_vars(cerr, *m_problem, b); }
            if (m_config.nra_proof) {
                m_config.nra_proof_out << "SAT with the following box:" << endl;
                pprint_vars(m_config.nra_proof_out, *m_problem, b);
                m_config.nra_proof_out << endl;
            }
            return true;
        } else {
            /* UNSAT */
            BOOST_LOG_TRIVIAL(debug) << "UNSAT!";
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
    out << "]" << endl;

    // collect all the ODE groups in the asserted literal and
    // print out
    unordered_set<int> ode_groups;
    for (auto const l : m_stack) {
        if (l->getPolarity() == l_True) {
            unordered_set<Enode*> const & odevars = m_odevars_in_lit[l];
            for (auto const var : odevars) {
                if (var->getODEvartype() == l_True) {
                    ode_groups.insert(var->getODEgroup());
                }
            }
        }
    }
    // for (auto const & p : m_env) {
    //     Enode* const key = p.first;
    //     double const lb =  p.second.first;
    //     double const ub =  p.second.second;
    //     if (starts_with(key->getCar()->getName(), "mode_")) {
    //         out << "Key: " << key << "\t Value: [" << lb << ", " << ub << "]" << endl;
    //     }
    // }
    out << ", \"groups\": [";
    for (auto g = ode_groups.cbegin(); g != ode_groups.cend(); g++) {
        if (g != ode_groups.cbegin()) {
            out << ", ";
        }
        out << *g;
    }
    out << "]" << endl << "}" << endl;
}
#endif
