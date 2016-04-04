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

#include <algorithm>
#include <iomanip>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include "util/hexfloat.h"
#include "util/logging.h"
#include "util/scoped_env.h"
#include "util/scoped_vec.h"
#include "dsolvers/icp_solver.h"
#include "dsolvers/heuristics/rp_splitter_hybrid.h"

using std::any_of;
using std::endl;
using std::find;
using std::min;
using std::numeric_limits;
using std::setfill;
using std::setw;
using std::stable_sort;
using std::streamsize;
using std::unordered_map;
using std::unordered_set;

namespace dreal {
icp_solver::icp_solver(SMTConfig & c, Egraph & e, SStore & t, scoped_vec const & stack, scoped_env & env, bool complete_check)
    : m_config(c), m_egraph(e), m_sstore(t),
      m_propag(&m_problem, 10.0, c.nra_verbose, c.nra_proof_out),
      m_boxes(env.size()), m_nsplit(0), m_stack(stack), m_env(env), m_complete_check(complete_check), m_num_delta_checks(0) {
    rp_init_library();
    m_problem = create_rp_problem();
    if ( !m_config.nra_use_delta_heuristic ){
        rp_new(m_vselect, rp_selector_existence, (&m_problem)); // rp_selector_roundrobin
    } else {
      if ( m_config.nra_ODE_sim_heuristic ){
        rp_new(m_vselect, rp_selector_delta_hybrid, (&m_problem)); // rp_selector_delta
        //      rp_new(m_vselect, rp_selector_delta, (&m_problem)); // rp_selector_delta
      } else{
        rp_new(m_vselect, rp_selector_delta, (&m_problem)); // rp_selector_delta
      }
    }
    if ( m_config.nra_ODE_sim_heuristic ){
      m_ode_sim_heuristic.initialize(m_propag, m_problem);
      rp_new(m_dsplit, rp_splitter_mixed_hybrid, (&m_problem)); // rp_splitter_mixed
      dynamic_cast<rp_splitter_mixed_hybrid*>(m_dsplit)->initialize(m_ode_sim_heuristic);
    } else{
      rp_new(m_dsplit, rp_splitter_mixed, (&m_problem)); // rp_splitter_mixed
    }
    // Check once the satisfiability of all the constraints
    // Necessary for variable-free constraints
    bool sat = true;
    for (int i = 0; i < rp_problem_nctr(m_problem); i++) {
        if (rp_constraint_unfeasible(rp_problem_ctr(m_problem, i), rp_problem_box(m_problem))) {
            sat = false;
            break;
        }
    }
    if (sat) {
        // Insertion of the initial box in the search structure
        m_boxes.insert(rp_problem_box(m_problem));
        // Management of improvement factor
        if ((c.nra_icp_improve >= 0.0) && (c.nra_icp_improve <= 100.0)) {
            m_improve = 1.0 - c.nra_icp_improve / 100.0;
        } else {
            m_improve = 0.875; /* 12.5% */
        }
        m_propag.set_improve(m_improve);
        // Creation of the operators and insertion in the propagator
        rp_hybrid_factory hfact(m_improve);
        hfact.apply(&m_problem, m_propag);
        rp_domain_factory dfact;
        dfact.apply(&m_problem, m_propag);
        rp_newton_factory nfact(m_improve);
        nfact.apply(&m_problem, m_propag);
        // Used for round-robin strategy: last variable split
        rp_box_set_split(m_boxes.get(), -1);// sean: why is the last variable -1? oh, must be length - this number
    } else {
        rp_box_set_empty(rp_problem_box(m_problem));
    }
#ifdef ODE_ENABLED
    if (m_complete_check && m_config.nra_ODE_contain) {
        create_ode_solvers();
    }
    if ( m_config.nra_ODE_sim_heuristic ){
      create_ode_sim_solvers();
    }
#endif
}

icp_solver::~icp_solver() {
    if (m_config.nra_delta_test) {
        DREAL_LOG_INFO << "icp_solver::~icp_solver: Number of delta checks: " << m_num_delta_checks;
    }
    rp_delete(m_vselect);
    rp_delete(m_dsplit);
    rp_reset_library();
#ifdef ODE_ENABLED
    for (ode_solver * s : m_ode_solvers)       { delete s; }
#endif
    rp_problem_destroy(&m_problem);
}

#ifdef ODE_ENABLED
void icp_solver::create_ode_sim_solvers() {
    // collect intergral and vector literals
    vector<Enode*> vec_integral;
    vector<Enode*> vec_inv;
    for (auto const l : m_stack) {
        // ignore if the polarity is "false".
        if (l->isIntegral() && l->getPolarity().toInt() == 1) {
            vec_integral.push_back(l);
        } else if (l->isForallT() && l->getPolarity().toInt() == 1) {
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
            unordered_set<Enode *> const vars_int = l_int->get_vars();
            unordered_set<Enode *> const vars_inv = l_inv->get_vars();
            bool intersect = any_of(vars_int.begin(), vars_int.end(), [&vars_inv](Enode * v_int) {
                    return find(vars_inv.begin(), vars_inv.end(), v_int) != vars_inv.end();
                });
            if (intersect) {
                invs.push_back(l_inv);
            }
        }
        m_ode_sim_heuristic.add_mode(m_config, m_egraph, l_int, // invs,
                                     m_enode_to_rp_id, m_rp_id_to_enode);
    }
}

void icp_solver::create_ode_solvers() {
    // collect intergral and vector literals
    vector<Enode*> vec_integral;
    vector<Enode*> vec_inv;
    for (auto const l : m_stack) {
        // ignore if the polarity is "false".
        if (l->isIntegral() && l->getPolarity().toInt() == 1) {
            vec_integral.push_back(l);
        } else if (l->isForallT() && l->getPolarity().toInt() == 1) {
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
            unordered_set<Enode *> const vars_int = l_int->get_vars();
            unordered_set<Enode *> const vars_inv = l_inv->get_vars();
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

rp_problem icp_solver::create_rp_problem() {
    rp_problem rp_prob;
    rp_problem_create(&rp_prob, "icp_holder");
    rp_prob->rp_icp_solver = this;
    // ======================================
    // Create rp_variable for each var in env
    // ======================================
    DREAL_LOG_INFO << "icp_solver::create_rp_problem: variables";
    rp_box_enlarge_size(&rp_problem_box(rp_prob), m_env.size());
    for (auto const & p : m_env) {
        Enode* const key = p.first;
        double const lb = p.second.lb;
        double const ub = p.second.ub;
        rp_variable  v;
        string const & name = key->getCar()->getName();
        rp_variable_create(&v, name.c_str());
        int const rp_id = rp_vector_insert(rp_table_symbol_vars(rp_problem_symb(rp_prob)), v);
        rp_bsup(rp_box_elem(rp_problem_box(rp_prob), rp_id)) = ub;
        rp_binf(rp_box_elem(rp_problem_box(rp_prob), rp_id)) = lb;
        rp_union_insert(rp_variable_domain(v), rp_box_elem(rp_problem_box(rp_prob), rp_id));
        if (key->hasSortInt()) {
            rp_variable_set_integer(v);
        } else if (key->hasSortReal()) {
            rp_variable_set_real(v);
            rp_variable_precision(v) = m_config.nra_precision;
        }
        m_enode_to_rp_id[key] = rp_id;
        m_rp_id_to_enode[rp_id] = key;
        if (DREAL_LOG_INFO_IS_ON) {
            string sort = "unknown";
            if (key->hasSortReal()) {
                sort = "Real";
            } else if (key->hasSortInt()) {
                sort = "Int";
            }
            DREAL_LOG_INFO << "\t"
                           << name << " : " << sort
                           << " = " << interval(lb, ub);
        }
    }

    // ===============================================
    // Create rp_constraints for each literal in stack
    // ===============================================
    DREAL_LOG_INFO << "icp_solver::create_rp_problem: constraints";
    for (auto const l : m_stack) {
        // Do not create rp_constraints for ForallT and Integral
        if (l->isForallT() || l->isIntegral()) { continue; }
        stringstream buf;
        l->print_infix(buf, l->getPolarity());
        string constraint_str = buf.str();
        if (constraint_str.compare("0 = 0") != 0) {
            rp_constraint c;
            DREAL_LOG_INFO << "icp_solver::create_rp_problem: constraint: " << (l->getPolarity() == l_True ? " " : "Not ") << l;
            // Parse the string (infix form) to create the constraint c
            rp_parse_constraint_string(&c, constraint_str.c_str(), rp_problem_symb(rp_prob));
            // set delta
            rp_ctr_set_delta(&c, (l->hasPrecision() ? l->getPrecision() : m_config.nra_precision));
            // Add to the problem
            rp_vector_insert(rp_problem_ctrs(rp_prob), c);
            // Update Counter
            for (int i = 0; i < rp_constraint_arity(c); ++i) {
                ++rp_variable_constrained(rp_problem_var(rp_prob, rp_constraint_var(c, i)));
            }
            m_enode_to_rp_ctr[l] = c;
        } else {
            m_enode_to_rp_ctr[l] = nullptr;
        }
    }
    DREAL_LOG_DEBUG << "icp_solver::create_rp_problem rp_problem_display";
    if (DREAL_LOG_DEBUG_IS_ON) {
        rp_problem_display(stderr, rp_prob);
    }
    return rp_prob;
}

#ifdef ODE_ENABLED
void icp_solver::callODESolver(ode_solver * odeSolver, bool forward, ode_solver::ODE_result & result) {
    // Simple ODE
    result = odeSolver->simple_ODE(m_boxes.get(), forward);

    if (result == ode_solver::ODE_result::UNSAT)
        return;
    if (!m_propag.apply(m_boxes.get())) {
        result = ode_solver::ODE_result::UNSAT;
        return;
    }

    if (forward) {
        // First Try (Forward).
        result = odeSolver->solve_forward(m_boxes.get());
        DREAL_LOG_DEBUG << "callODESolver: solve_forward result = " << result;
        if (result == ode_solver::ODE_result::UNSAT)
            return;
        if (!m_propag.apply(m_boxes.get())) {
            result = ode_solver::ODE_result::UNSAT;
            return;
        }
        // Second Try (Backward).
        result = odeSolver->solve_backward(m_boxes.get());
        DREAL_LOG_DEBUG << "callODESolver: solve_backward result = " << result;
        if (result == ode_solver::ODE_result::UNSAT)
            return;
        if (!m_propag.apply(m_boxes.get())) {
            result = ode_solver::ODE_result::UNSAT;
            return;
        }
    } else {
        // First Try (Backward).
        result = odeSolver->solve_backward(m_boxes.get());
        DREAL_LOG_DEBUG << "callODESolver: solve_backward result = " << result;
        if (result == ode_solver::ODE_result::UNSAT)
            return;
        if (!m_propag.apply(m_boxes.get())) {
            result = ode_solver::ODE_result::UNSAT;
            return;
        }
        // Second Try (Forward).
        result = odeSolver->solve_forward(m_boxes.get());
        DREAL_LOG_DEBUG << "callODESolver: solve_forward result = " << result;
        if (result == ode_solver::ODE_result::UNSAT)
            return;
        if (!m_propag.apply(m_boxes.get())) {
            result = ode_solver::ODE_result::UNSAT;
            return;
        }
    }
    return;
}
#endif

bool icp_solver::prop_with_ODE() {
  DREAL_LOG_INFO << "icp_solver::prop_with_ODE()";
    if (m_propag.apply(m_boxes.get())) {
#ifdef ODE_ENABLED
        if (m_config.nra_ODE_contain) {
            // Sort ODE Solvers by their logVolume.
            sort(m_ode_solvers.begin(), m_ode_solvers.end(),
                 [this](ode_solver * odeSolver1, ode_solver * odeSolver2) {
                   rp_box b = m_boxes.get();
                   double const min1 = min(odeSolver1->logVolume_X0(b), odeSolver1->logVolume_Xt(b));
                   double const min2 = min(odeSolver2->logVolume_X0(b), odeSolver2->logVolume_Xt(b));
                   return min1 < min2;
                   // return odeSolver1->step() < odeSolver2->step();
                 });
            for (auto const & odeSolver : m_ode_solvers) {
                rp_box b = m_boxes.get();
                double const lv_x0 = odeSolver->logVolume_X0(b);
                double const lv_xt = odeSolver->logVolume_Xt(b);
                unsigned const mode = odeSolver->get_Mode();
                bool forward = m_config.nra_ODE_forward_only ? true : lv_x0 <= lv_xt;
                DREAL_LOG_INFO << "icp_solver::prop_with_ODE: " << mode << "\t" << lv_x0 << "\t"<< lv_xt
                               << "\t" << (forward ? "Forward" : "Backward");
                stringstream ss;
                pprint_vars(ss, m_problem, b, false);
                DREAL_LOG_DEBUG << ss.str();
                ode_solver::ODE_result result = ode_solver::ODE_result::SAT;
                callODESolver(odeSolver, forward, result);
                if (result == ode_solver::ODE_result::UNSAT) {
                    return false;
                }
            }
        }
#endif
        return true;
    }
    return false;
}

double icp_solver::constraint_width(const rp_constraint * c, rp_box const b) const {
    rp_ctr_num const c_num = rp_constraint_num(*c);
    rp_erep const lhs = rp_expression_rep(rp_ctr_num_left(c_num));
    rp_erep const rhs = rp_expression_rep(rp_ctr_num_right(c_num));
    rp_erep lhs_minus_rhs_rep;
    rp_erep_create_binary (&lhs_minus_rhs_rep, RP_SYMBOL_SUB, lhs, rhs);
    rp_expression lhs_minus_rhs;
    double res = 0.0;
    rp_expression_create(&lhs_minus_rhs, &lhs_minus_rhs_rep);
    if (rp_expression_eval(lhs_minus_rhs, b)) {
        res = rp_interval_width(rp_expression_val(lhs_minus_rhs));
    }
    rp_expression_destroy(&lhs_minus_rhs);
    return res;
}

int icp_solver::get_var_split_delta(rp_box b) {
    // get constraint with max residual width
    int i = 0, max_constraint = -1;
    double max_width = 0.0;
    for (Enode * const l : m_stack) {
        if (l->isForallT() || l->isIntegral()) {
            continue;
        }
        stringstream buf;
        l->print_infix(buf, l->getPolarity());
        string constraint_str = buf.str();
        DREAL_LOG_INFO << "icp_solver::get_var_split_delta: Considering constraint" << constraint_str;
        if (constraint_str.compare("0 = 0") != 0) {
            rp_constraint const c = rp_problem_ctr(m_problem, i);
            double const width =  constraint_width(&c, b);
            double const residual = width - rp_constraint_delta(c);
            if (residual > max_width) {
                max_width = residual;
                max_constraint = i;
                l->print_infix(buf, l->getPolarity());
            }
            i++;
        }
    }
    if (max_constraint > -1) {
        // get var with max width in max width constraint
        const rp_constraint c = rp_problem_ctr(m_problem, max_constraint);
        max_width = 0.0;
        int max_var = -1;
        for (i = 0; i < rp_constraint_arity(c); i++){
            int const var = rp_constraint_var(c, i);
            double const width = rp_interval_width(rp_box_elem(b, var));
            if (width > max_width) {
                max_width = width;
                max_var = var;
            }
        }
        Enode* lit = m_rp_id_to_enode[max_var];
        DREAL_LOG_INFO << "icp_solver::get_var_split_delta: Delta Split: " << max_var << " " << lit;
        return max_var;
    } else {
        DREAL_LOG_INFO << "icp_solver::get_var_split_delta: Delta Split: -1";
        return -1;
    }
}


  // get the maximum time index of any variable in constraint
  int icp_solver::get_max_time_index(rp_constraint c){
    int max = -1;
    for (int i = 0; i < rp_constraint_arity(c); i++){
      int const var = rp_constraint_var(c, i);

      Enode* v = m_rp_id_to_enode[var];
      stringstream ss;
      ss << v;
      string svar = ss.str();
      // time index is first number after an "_"
      int start = svar.find("_")+1;
      int end = svar.find("_", start)-1;
      if ((const size_t) end == string::npos)
        end = svar.size();
      int time =  atoi(svar.substr(start, end).c_str());
      //      DREAL_LOG_INFO << "time("<< svar << ") = " << time;
      if ( time > max )
        max = time;
    }
    return max;
  }

int icp_solver::get_var_split_delta_hybrid(rp_box b) {
    // get constraints by time index

  DREAL_LOG_DEBUG << "icp_solver::get_var_split_delta_hybrid()";
  // collect constraints that are loose and fall within the same minimum maximum time step
  // of these constraints pick the loosest.

    int i = 0, max_constraint = -1;
    double max_width = 0.0;
    int min_max_time_index = INT_MAX;
    for (Enode * const l : m_stack) {
        if (l->isForallT() || l->isIntegral()) {
            continue;
        }
        stringstream buf;
        l->print_infix(buf, l->getPolarity());
        string constraint_str = buf.str();
        if (constraint_str.compare("0 = 0") != 0) {
            const rp_constraint c = rp_problem_ctr(m_problem, i);

            int max_time_index = get_max_time_index(c);
            double const width =  constraint_width(&c, b);
            double const residual = width - rp_constraint_delta(c);

            if (max_time_index <= min_max_time_index && width > 2.0*rp_constraint_delta(c)){
              if (max_time_index < min_max_time_index){
                max_width = 0;
              }
              min_max_time_index = max_time_index;
              if (residual > max_width) {
                DREAL_LOG_INFO << "icp_solver::get_var_split_delta: Considering constraint "
                               << constraint_str
                               << " max_time = " << max_time_index
                               << " width = " << width
                               << " residual = " << residual;
                max_width = residual;
                max_constraint = i;
                l->print_infix(buf, l->getPolarity());
                string constraint_str = buf.str();
              }
            }
            i++;
        }
    }
    if (max_constraint > -1) {
        // get var with max width in max width constraint
        const rp_constraint c = rp_problem_ctr(m_problem, max_constraint);
        max_width = 0.0;
        int max_var = -1;
        for (i = 0; i < rp_constraint_arity(c); i++){
            int const var = rp_constraint_var(c, i);
            double const width = rp_interval_width(rp_box_elem(b, var));
            if (width > max_width) {
                max_width = width;
                max_var = var;
            }
        }
        Enode* lit = m_rp_id_to_enode[max_var];
        DREAL_LOG_INFO << "icp_solver::get_var_split_delta: Delta Split: " << max_var << " " << lit;
        return max_var;
    } else {
        DREAL_LOG_INFO << "icp_solver::get_var_split_delta: Delta Split: -1";
        return -1;
    }
}

bool icp_solver::is_box_within_delta(rp_box b) {
    // for each expression
    //  compute width given box
    //  check if expression width <= delta
  //  DREAL_LOG_INFO << "icp_solver::is_box_within_delta: Checking box width...";
    m_num_delta_checks++;

    int i = 0;
    bool fail = false;
    for (auto const l : m_stack) {
        if (l->isForallT() || l->isIntegral()) {
            continue;
        }
        stringstream buf;
        l->print_infix(buf, l->getPolarity());
        string constraint_str = buf.str();
        if (constraint_str.compare("0 = 0") != 0) {
            const rp_constraint c = rp_problem_ctr(m_problem, i);
            double width =  constraint_width(&c, b);
            bool test = width > 2.0*rp_constraint_delta(c);
            if (test){
                // DREAL_LOG_INFO << "icp_solver::is_box_within_delta: " <<  i << ": "
                //                << constraint_str
                //                << "\t: [" << width << " <= "
                //                << 2.0 *rp_constraint_delta(c)
                //                << "]\t"
                //                << (width - 2.0*rp_constraint_delta(c));
            }
            if ( test ){
                fail = true;
                // break;
            }
            // d++;
            i++;
        }
    }
    DREAL_LOG_INFO << "icp_solver::is_box_within_delta: Within Delta = " << (!fail);
    return !fail; // no constraint width is outside of delta or unsat
}

rp_box icp_solver::compute_next() {
    while (!m_boxes.empty()) {
        if (prop_with_ODE()) { // sean: here it is! propagation before split!!!
            // SAT => Split
            rp_box b = m_boxes.get();
            int i = m_vselect->apply(b);
            DREAL_LOG_INFO << "Split Var: " << i;
            if (i >= 0 &&
                ((m_config.nra_delta_test ?
                  !is_box_within_delta(b) :
                  rp_box_width(b) >= m_config.nra_precision))) {
                if (m_config.nra_proof) {
                    m_config.nra_proof_out << endl
                                           << "[branched on "
                                           << rp_variable_name(rp_problem_var(m_problem, i))
                                           << "]"
                                           << endl;
                    pprint_vars(m_config.nra_proof_out, m_problem, b, true);
                }
                ++m_nsplit;
                m_dsplit->apply(m_boxes, i);

                DREAL_LOG_INFO << "icp_solver::compute_next: branched on " << rp_variable_name(rp_problem_var(m_problem, i));
                //                cout << rp_variable_name(rp_problem_var(m_problem, i)) << endl;

            } else {
                return(b);
            }
        } else {
            // UNSAT => Remove box
          //          cout << "/" << std::endl;
          DREAL_LOG_INFO << "***************** Not branched on Found UNSAT box ***********";
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
    if (rp_box_empty(rp_problem_box(m_problem))) {
        DREAL_LOG_INFO << "icp_solver::solve: Unfeasibility detected before solving";
        return false;
    } else {
        rp_box b = compute_next();
        if (b != nullptr) {
            /* SAT */
            DREAL_LOG_INFO << "icp_solver::solve: SAT with the following box:";
            if (DREAL_LOG_INFO_IS_ON) {
                pprint_vars(cerr, m_problem, b, false);
                if (m_config.nra_delta_test) {
                    pprint_lits(cerr, m_problem, b);
                }
            }
            if (m_config.nra_proof) {
                m_config.nra_proof_out.close();
                m_config.nra_proof_out.open(m_config.nra_proof_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
                m_config.nra_proof_out << "SAT with the following box:" << endl;
                pprint_vars(m_config.nra_proof_out, m_problem, b, false);
                if (m_config.nra_delta_test) {
                    pprint_lits(m_config.nra_proof_out, m_problem, b);
                }
                m_config.nra_proof_out << endl;
            }
            if (m_config.nra_model) {
                m_config.nra_model_out.open (m_config.nra_model_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
                if (m_config.nra_model_out.fail()) {
                    cout << "Cannot create a file: " << m_config.nra_model_out_name << endl;
                    exit(1);
                }
                m_config.nra_model_out << "SAT with the following box:" << endl;
                pprint_vars(m_config.nra_model_out, m_problem, b, false);
            }
            return true;
        } else {
            /* UNSAT */
            DREAL_LOG_INFO << "icp_solver::solve: UNSAT";
            return false;
        }
    }
}

void display_number(ostream & out, double x, int digits, bool exact) {
    if (exact) {
        out << to_hexfloat(x);
    } else {
        streamsize ss = out.precision();
        out.precision(digits);
        out << x;
        out.precision(ss);
    }
}

void icp_solver::display_interval(ostream & out, rp_interval i, int digits, bool exact) const {
    static interval tmp;
    tmp.lb = rp_binf(i);
    tmp.ub = rp_bsup(i);
    tmp.print(out, digits, exact);
}

void icp_solver::pprint_vars(ostream & out, rp_problem p, rp_box b, bool exact) const {
    for (int i = 0; i <rp_problem_nvar(p); i++) {
        out << setw(15);
        out << rp_variable_name(rp_problem_var(p, i));
        out << " : ";
        display_interval(out, rp_box_elem(b, i), 16, exact);
        if (i != rp_problem_nvar(p) - 1)
            out << ";";
        out << endl;
    }
}

void icp_solver::pprint_lits(ostream & out, rp_problem p, rp_box b) const {
    int i = 0;
    for (auto const l : m_stack) {
        if (l->isForallT() || l->isIntegral()) {
            continue;
        }
        stringstream buf;
        l->print_infix(buf, l->getPolarity());
        string constraint_str = buf.str();
        if (constraint_str.compare("0 = 0") != 0) {
            rp_constraint c = rp_problem_ctr(p, i);
            out << i << ": " <<   constraint_str << "\t: "
                << constraint_width(&c, b);
            out << ";";
            out << " [delta = " << rp_constraint_delta(c) << "]";
            out << endl;
            i++;
        }
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
    m_config.nra_proof_out << m_env << endl;
}

// return true if the box is non-empty after propagation
// false if the box is *empty* after propagation
bool icp_solver::prop() {
    bool result = false;
    if (m_config.nra_proof) { output_problem(); }
    if (!m_boxes.empty()) { result = m_propag.apply(m_boxes.get()); }
    if (!result) {
        // UNSAT
        if (m_config.nra_proof) { m_config.nra_proof_out << "[conflict detected]" << endl; }
        DREAL_LOG_INFO << "[conflict detected]";
    } else {
        // SAT, Update Env
        rp_box const b = m_boxes.get();
        for (auto const & p : m_env) {
            Enode* const key = p.first;
            int const rp_id = m_enode_to_rp_id[key];
            m_env.update(key, interval(rp_binf(rp_box_elem(b, rp_id)),
                                       rp_bsup(rp_box_elem(b, rp_id))));
        }
        if (m_config.nra_proof) { m_config.nra_proof_out << "HOLE" << endl; }
    }
    return result;
}

vector<Enode *> icp_solver::get_explanation() {
    vector<Enode *> explanation;
    for (Enode * const l : m_stack) {
        if (m_enode_to_rp_ctr.find(l) != m_enode_to_rp_ctr.end()) {
            rp_constraint const c = m_enode_to_rp_ctr[l];
            // if the constraint is "0 = 0" (= trivial), we have c ==
            // nullptr and do not add it in the explanation
            if (c == nullptr) continue;
            assert(rp_constraint_type(c) == RP_CONSTRAINT_NUMERICAL);
            rp_ctr_num cnum = rp_constraint_num(c);
            if (rp_ctr_num_used(cnum)) {
                explanation.push_back(l);
                DREAL_LOG_DEBUG << "icp_solver::build_explanation: " << l;
            } else {
                DREAL_LOG_DEBUG << "icp_solver::build_explanation: SKIP " << l;
            }
        } else {
            // For ODE literals (intergral, forall_t), we don't have
            // an entry in m_enode_to_rp_ctr. For now, we always add
            // them to the explanation to make it sound. Later we may
            // implement a better explanation for them.
            explanation.push_back(l);
            DREAL_LOG_DEBUG << "icp_solver::build_explanation: [ODE] " << l;
        }
    }
    return explanation;
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
}
