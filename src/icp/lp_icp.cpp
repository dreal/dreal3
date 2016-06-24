/*********************************************************************
Author: Damien Zufferey <zufferey@csail.mit.edu>
        Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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

#include <tuple>
#include <unordered_set>
#include <vector>
#include <stack>
#include "./config.h"
#include "icp/icp.h"
#include "icp/lp_icp.h"
#include "icp/brancher.h"
#include "constraint/constraint.h"
#include "util/logging.h"
#include "util/scoped_vec.h"
#include "util/stat.h"
#include "util/glpk_wrapper.h"

using std::cerr;
using std::cout;
using std::endl;
using std::get;
using std::tuple;
using std::unordered_set;
using std::shared_ptr;
using std::vector;
using std::stack;

#ifdef USE_GLPK

namespace dreal {

enum class lp_icp_kind { LP, ICP };

SizeBrancher lp_sb;
BranchHeuristic & lp_icp::defaultHeuristic = lp_sb;

bool lp_icp::is_lp_sat(glpk_wrapper & lp_solver, box & solution, SMTConfig const & config) {
  if (!lp_solver.is_sat()) {
    if (lp_solver.certify_unsat(config.nra_precision)) {
      DREAL_LOG_FATAL << "lp_icp: LP say unsat";
      return false;
    } else {
      lp_solver.use_exact();
      if (!lp_solver.is_sat()) {
        DREAL_LOG_FATAL << "lp_icp: LP say unsat (using exact solver)";
        lp_solver.use_simplex();
        return false;
      } else {
        lp_solver.get_solution(solution);
        lp_solver.use_simplex();
        return true;
      }
    }
  } else {
    lp_solver.get_solution(solution);
    return true;
  }
}

void lp_icp::solve(contractor & ctc, contractor_status & cs,
                  scoped_vec<shared_ptr<constraint>>& constraints,
                  BranchHeuristic& brancher) {
    thread_local static vector<box> solns;
    /* The stack now contains both the LP and ICP domain.
     * For the ICP, the stack is the usual DFS worklist.
     * For the LP, the stack is keeping track of the state of the previous domain.
     * That way we know how to backtrack and set the old domain back.
     * Invariant: all the boxes on the stack have been pruned
     * Invariant: the LP boxes contains all the ICP boxes above them
     */
    thread_local static stack<tuple<lp_icp_kind, box>> box_stack;
    // a "box" for the point solution of the lp_solver
    thread_local static box lp_point(cs.m_box);
    solns.clear();
    stack<tuple<lp_icp_kind, box>>().swap(box_stack); // clear up box_stack

    // all the box on the stack must be pruned
    ctc.prune(cs);
    if (cs.m_config.nra_use_stat) { cs.m_config.nra_stat.increase_prune(); }
    if (!cs.m_box.is_empty()) {
        box_stack.emplace(lp_icp_kind::ICP, cs.m_box);
    } else {
        return;
    }

    // create the LP with the linear constraints
    unordered_set<Enode*> es;
    for (auto cptr : constraints) {
        if (cptr->get_type() == constraint_type::Nonlinear) {
            auto ncptr = std::dynamic_pointer_cast<nonlinear_constraint>(cptr);
            auto e = ncptr->get_enode();
            if (glpk_wrapper::is_linear(e)) {
                DREAL_LOG_FATAL << "lp_icp:     linear: " << e;
                es.insert(e);
            } else {
                DREAL_LOG_FATAL << "lp_icp: not linear: " << e;
            }
        }
    }
    glpk_wrapper lp_solver(cs.m_box, es);


    while (!box_stack.empty()) {
        DREAL_LOG_FATAL << "lp_icp::solve - loop"
                        << "\t" << "box stack Size = " << box_stack.size();
        tuple<lp_icp_kind, box> branch = box_stack.top();
        box_stack.pop();
        lp_icp_kind kind = get<0>(branch);
        cs.m_box = get<1>(branch);

        switch (kind) {
        case lp_icp_kind::LP:
            lp_solver.set_domain(cs.m_box);
            break;
        case lp_icp_kind::ICP:
            if (!is_lp_sat(lp_solver, lp_point, cs.m_config)) {
                assert(cs.m_box.is_subset(lp_solver.get_domain()));
                cs.m_box.set_empty();
            } else {
                if (lp_point.is_subset(cs.m_box)) {
                    if (cs.m_config.nra_use_stat) { cs.m_config.nra_stat.increase_branch(); }
                    vector<int> const sorted_dims = brancher.sort_branches(cs.m_box, constraints, cs.m_config, 1);
                    if (sorted_dims.size() > 0) {
                        // branch ...
                        int const i = sorted_dims[0];
                        tuple<int, box, box> const splits = cs.m_box.bisect_at(sorted_dims[0]);
                        if (cs.m_config.nra_proof) {
                            cs.m_config.nra_proof_out << "[branched on "
                                                      << cs.m_box.get_name(i)
                                                      << "]" << endl;
                        }
                        // ... and prune
                        contractor_status cs1(get<1>(splits), cs.m_config);
                        ctc.prune(cs1);
                        if (cs.m_config.nra_use_stat) { cs.m_config.nra_stat.increase_prune(); }
                        contractor_status cs2(get<2>(splits), cs.m_config);
                        ctc.prune(cs2);
                        if (cs.m_config.nra_use_stat) { cs.m_config.nra_stat.increase_prune(); }

                        // push the non-empty boxes on the stack
                        if (!cs1.m_box.is_empty()) {
                            if (!cs2.m_box.is_empty()) {
                                // try to go where the LP says there is a solution
                                if (lp_point.is_subset(cs1.m_box)) {
                                    box_stack.emplace(lp_icp_kind::ICP, cs2.m_box);
                                    box_stack.emplace(lp_icp_kind::ICP, cs1.m_box);
                                } else {
                                    box_stack.emplace(lp_icp_kind::ICP, cs1.m_box);
                                    box_stack.emplace(lp_icp_kind::ICP, cs2.m_box);
                                }
                            } else {
                                box_stack.emplace(lp_icp_kind::ICP, cs1.m_box);
                            }
                        } else {
                            if (!cs2.m_box.is_empty()) {
                                box_stack.emplace(lp_icp_kind::ICP, cs2.m_box);
                            }
                        }
                    } else {
                        // box is not bisectable, we have a solution
                        cs.m_config.nra_found_soln++;
                        if (cs.m_config.nra_multiple_soln > 1) {
                            // If --multiple_soln is used
                            output_solution(cs.m_box, cs.m_config, cs.m_config.nra_found_soln);
                        }
                        if (cs.m_config.nra_found_soln >= cs.m_config.nra_multiple_soln) {
                            break;
                        }
                        solns.push_back(cs.m_box);
                    }
                } else {
                    // the point solution of the LP is not is the current box.
                    // set the LP domain to the current box.
                    DREAL_LOG_DEBUG << "lp_icp::solve - asking for a new point solution";
                    box_stack.emplace(lp_icp_kind::LP, lp_solver.get_domain());
                    lp_solver.set_domain(cs.m_box);
                    box_stack.emplace(lp_icp_kind::ICP, cs.m_box);
                }
            }
            break;  // end of case LP:
        }  // end of switch
        // make b empty in case the stack is empty
        b.set_empty();
    }  // end of while

    if (cs.m_config.nra_multiple_soln > 1 && solns.size() > 0) {
        cs.m_box = solns.back();
        return;
    } else {
        assert(!cs.m_box.is_empty() || box_stack.size() == 0);
        return;
    }
}

}  // namespace dreal
#endif
