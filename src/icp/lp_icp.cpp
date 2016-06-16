/*********************************************************************
Author: Damien Zufferey <zufferey@csail.mit.edu>

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

#define LP true
#define ICP false

SizeBrancher lp_sb;
BranchHeuristic & lp_icp::defaultHeuristic = lp_sb;

bool lp_icp::is_lp_sat(glpk_wrapper & lp_solver, box & solution, SMTConfig const & config) {
  if (!lp_solver.is_sat()) {
    if (lp_solver.certify_unsat(config.nra_precision)) {
      DREAL_LOG_INFO << "lp_icp: LP say unsat";
      return false;
    } else {
      lp_solver.use_exact();
      if (!lp_solver.is_sat()) {
        DREAL_LOG_INFO << "lp_icp: LP say unsat (using exact solver)";
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

box lp_icp::solve(box b, contractor & ctc,
        scoped_vec<shared_ptr<constraint>>& constraints,
        SMTConfig & config,
        BranchHeuristic& brancher) {
    thread_local static vector<box> solns;
    /* The stack now contains both the LP and ICP domain.
     * For the ICP, the stack is the usual DFS worklist.
     * For the LP, the stack is keeping track of the state of the previous domain.
     * That way we know how to backtrack and set the old domain back.
     * Invariant: all the boxes on the stack have been pruned
     * Invariant: the LP boxes contains all the ICP boxes above them
     */
    thread_local static stack<tuple<bool, box>> box_stack;
    // a "box" for the point solution of the lp_solver
    thread_local static box lp_point(b);

    solns.clear();
    while (!box_stack.empty()) {
        box_stack.pop();
    }

    // all the box on the stack must be pruned
    ctc.prune(b, config);
    if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
    if (!b.is_empty()) {
        box_stack.emplace(ICP, b);
    } else {
        return b;
    }

    // create the LP with the linear constraints
    unordered_set<Enode*> es;
    for (auto cptr : constraints) {
        if (cptr->get_type() == constraint_type::Nonlinear) {
            auto ncptr = std::dynamic_pointer_cast<nonlinear_constraint>(cptr);
            auto e = ncptr->get_enode();
            if (glpk_wrapper::is_linear(e)) {
                DREAL_LOG_INFO << "lp_icp:     linear: " << e;
                es.insert(e);
            } else {
                DREAL_LOG_INFO << "lp_icp: not linear: " << e;
            }
        }
    }
    glpk_wrapper lp_solver(b, es);


    while (!box_stack.empty()) {
        DREAL_LOG_INFO << "lp_icp::solve - loop"
                       << "\t" << "box stack Size = " << box_stack.size();
        tuple<unsigned, box> branch = box_stack.top();
        box_stack.pop();
        bool kind = get<0>(branch);
        b = get<1>(branch);

        if (kind == LP) {
            lp_solver.set_domain(b);
        } else if (!is_lp_sat(lp_solver, lp_point, config)) {
            assert(b.is_subset(lp_solver.get_domain()));
            b.set_empty();
        } else {

            if (lp_point.is_subset(b)) {
                if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
                vector<int> sorted_dims = brancher.sort_branches(b, constraints, config);
                if (sorted_dims.size() > 0) {
                    // branch ...
                    int const i = sorted_dims[0];
                    tuple<int, box, box> splits = b.bisect_at(sorted_dims[0]);
                    if (config.nra_proof) {
                        config.nra_proof_out << "[branched on "
                                             << b.get_name(i)
                                             << "]" << endl;
                    }
                    // ... and prune
                    box & first  = get<1>(splits);
                    box & second = get<2>(splits);
                    ctc.prune(first, config);
                    if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
                    ctc.prune(second, config);
                    if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
                    // push the non-empty boxes on the stack
                    if (!first.is_empty()) {
                        if (!second.is_empty()) {
                            // try to go where the LP says there is a solution
                            if (lp_point.is_subset(first)) {
                                box_stack.emplace(ICP, second);
                                box_stack.emplace(ICP, first);
                            } else {
                                box_stack.emplace(ICP, first);
                                box_stack.emplace(ICP, second);
                            }
                        } else {
                            box_stack.emplace(ICP, first);
                        }
                    } else {
                        if (!second.is_empty()) {
                            box_stack.emplace(ICP, second);
                        }
                    }

                } else {
                    // box is not bisectable, we have a solution
                    config.nra_found_soln++;
                    if (config.nra_multiple_soln > 1) {
                        // If --multiple_soln is used
                        output_solution(b, config, config.nra_found_soln);
                    }
                    if (config.nra_found_soln >= config.nra_multiple_soln) {
                        break;
                    }
                    solns.push_back(b);
                }
            } else {
                // the point solution of the LP is not is the current box.
                // set the LP domain to the current box.
                box_stack.emplace(LP, lp_solver.get_domain());
                lp_solver.set_domain(b);
                box_stack.emplace(ICP, b);
            }
        }
    }

    if (config.nra_multiple_soln > 1 && solns.size() > 0) {
        return solns.back();
    } else {
        assert(!b.is_empty() || box_stack.size() == 0);
        return b;
    }
}

}  // namespace dreal
#endif
