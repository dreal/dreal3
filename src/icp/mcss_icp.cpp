/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@mit.edu>

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

#include "icp/mcss_icp.h"

#include <assert.h>
#include <memory>
#include <ostream>
#include <tuple>
#include <vector>

#include "contractor/contractor.h"
#include "contractor/contractor_status.h"
#include "icp/brancher.h"
#include "icp/icp_util.h"
#include "smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/stacker.h"
#include "util/stat.h"
#include "util/thread_local.h"

namespace dreal {
class constraint;
template <typename T>
class scoped_vec;
}  // namespace dreal

using std::endl;
using std::get;
using std::shared_ptr;
using std::tuple;
using std::vector;
namespace dreal {
static SizeBrancher sb;
BranchHeuristic & mcss_icp::defaultHeuristic = sb;

void mcss_icp::solve(contractor & ctc, contractor_status & cs,
                     scoped_vec<shared_ptr<constraint>> const & ctrs, BranchHeuristic & brancher) {
    DREAL_THREAD_LOCAL static vector<box> solns;
    DREAL_THREAD_LOCAL static vector<box> box_stack;
    solns.clear();
    box_stack.clear();
    box_stack.push_back(cs.m_box);
    double const prec = cs.m_config.nra_delta_test ? 0.0 : cs.m_config.nra_precision;
    stacker stack(box_stack, ctrs, prec);
    double tmp_score = 0.0;
    DREAL_LOG_INFO << "----new mcss instance----";
    do {
        DREAL_LOG_INFO << "mcss_icp::solve - loop"
                       << "\t"
                       << "box stack Size = " << box_stack.size();
        if (!stack.playout()) {
            cs.m_box = stack.pop_best();
            tmp_score = stack.get_best_score();
            DREAL_LOG_INFO << "best score right now: " << tmp_score << "\t";
        } else {
            cs.m_config.nra_found_soln++;
            if (cs.m_config.nra_multiple_soln > 1) {
                // If --multiple_soln is used
                output_solution(cs.m_box, cs.m_config, cs.m_config.nra_found_soln);
            }
            cs.m_box = stack.get_solution();
            DREAL_LOG_INFO << "mcss found solution\n" << cs.m_box;
            if (cs.m_config.nra_found_soln >= cs.m_config.nra_multiple_soln) {
                break;
            }
            solns.push_back(cs.m_box);
        }
        prune(ctc, cs);
        if (!cs.m_box.is_empty()) {
            vector<int> const sorted_dims =
                brancher.sort_branches(cs.m_box, ctrs, ctc.get_input(), cs.m_config, 1);
            if (sorted_dims.size() > 0) {
                int const i = sorted_dims[0];
                tuple<int, box, box> splits = cs.m_box.bisect_at(sorted_dims[0]);
                if (cs.m_config.nra_use_stat) {
                    cs.m_config.nra_stat.increase_branch();
                }
                // After branching, we prune each box and put into stack.
                contractor_status cs1(cs, get<1>(splits));
                contractor_status cs2(cs, get<2>(splits));
                prune(ctc, cs1);
                prune(ctc, cs2);
                box & first = cs1.m_box;
                box & second = cs2.m_box;
                assert(first.get_idx_last_branched() == i);
                assert(second.get_idx_last_branched() == i);
                if (!first.is_empty()) {
                    first.test_score(tmp_score);
                    stack.push(first);
                }
                if (!second.is_empty()) {
                    second.test_score(tmp_score);
                    stack.push(second);
                }
                if (cs.m_config.nra_proof) {
                    cs.m_config.nra_proof_out << "[branched on " << cs.m_box.get_name(i) << "]"
                                              << endl;
                }
            } else {
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
        }
    } while (stack.get_size() > 0);
    if (cs.m_config.nra_multiple_soln > 1 && solns.size() > 0) {
        cs.m_box = solns.back();
        return;
    } else {
        assert(!cs.m_box.is_empty() || box_stack.size() == 0);
        return;
    }
}
}  // namespace dreal
