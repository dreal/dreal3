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

#include "icp/scoring_icp.h"

#include <assert.h>
#include <algorithm>
#include <memory>
#include <ostream>
#include <string>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "contractor/contractor_status.h"
#include "ibex_Interval.h"
#include "icp/brancher.h"
#include "icp/icp.h"
#include "smtsolvers/SMTConfig.h"
#include "util/logging.h"
#include "util/stat.h"
#include "util/thread_local.h"

namespace dreal {
class constraint;
template <typename T>
class scoped_vec;
}  // namespace dreal

using std::get;
using std::endl;
using std::shared_ptr;
using std::tuple;
using std::unordered_set;
using std::vector;

namespace dreal {

SizeBrancher scoring_sb;
BranchHeuristic & scoring_icp::defaultHeuristic = scoring_sb;

void scoring_icp::reset_scores() {
    for (unsigned int i = 0; i < size; i++) {
        scores[i] = 1;
        prune_results[i] = 0;
        nbr_prune[i] = 0;
    }
}

void scoring_icp::compute_scores() {
    for (unsigned int i = 0; i < size; i++) {
        double new_score = 1;
        if (nbr_prune[i] > 0) {
            new_score = std::min(1000.0, nbr_prune[i] / prune_results[i]);
            nbr_prune[i] = 0;
            prune_results[i] = 0;
        }
        scores[i] = score_update_old_weight * scores[i] + (1 - score_update_old_weight) * new_score;
        DREAL_LOG_INFO << "score of " << cs.m_box.get_name(i) << " is\t" << scores[i];
    }
}

int scoring_icp::highest_score() {
    int max_idx = -1;
    double max_score = 1;
    for (unsigned int i = 0; i < size; i++) {
        if (cs.m_box.is_bisectable_at(i, cs.m_config.nra_precision)) {
            double s = scores[i];
            if (s > max_score) {
                max_idx = i;
                max_score = s;
            }
        }
    }
    DREAL_LOG_DEBUG << "highest_score " << max_idx << " with " << max_score;
    return max_idx;
}

double scoring_icp::measure(box const & o, box const & n) {
    if (n.is_empty()) {
        return 0.0;
    } else {
        unsigned int s = o.size();
        double val = 0.0;
        for (unsigned int i = 0; i < s; i++) {
            double rn = n[i].rad();
            double ro = o[i].rad();
            if (rn > 0.0) {
                val += rn / ro;
            } else if (ro <= 0.0) {
                val += 1;
            }
        }
        return val / s;
    }
}

void scoring_icp::safe_prune(int idx) {
    try {
        DREAL_THREAD_LOCAL static box old_box = cs.m_box;
        ctc.prune(cs);
        if (cs.m_config.nra_use_stat) {
            cs.m_config.nra_stat.increase_prune();
        }
        if (idx >= 0) {
            prune_results[idx] += measure(old_box, cs.m_box);
            nbr_prune[idx] += 1;
        }
    } catch (contractor_exception & e) {
        // Do nothing
    }
}

void scoring_icp::prune_split_fixed_point() {
    DREAL_THREAD_LOCAL static box tmp = cs.m_box;
    DREAL_THREAD_LOCAL static box progress = tmp;
    unsigned int s = cs.m_box.size();
    int n = 0;
    do {
        if (cs.m_box.is_empty()) {
            break;
        }
        n++;
        progress = cs.m_box;
        for (unsigned int i = 0; i < s && !cs.m_box.is_empty(); i++) {
            if (cs.m_box.is_bisectable_at(i, cs.m_config.nra_precision)) {
                tuple<int, box, box> splits = cs.m_box.bisect_at(i);
                cs.m_box = get<1>(splits);
                safe_prune(i);
                tmp = cs.m_box;
                cs.m_box = get<2>(splits);
                safe_prune(i);
                cs.m_box.hull(tmp);
            }
        }
        DREAL_LOG_INFO << measure(progress, cs.m_box) << (cs.m_box.is_empty() ? "\t✓" : "\t✗");
    } while (measure(progress, cs.m_box) < progress_threshold);
    DREAL_LOG_INFO << "prune_split_fixed_point: " << n;
}

void scoring_icp::solve() {
    box_stack.emplace(0, cs.m_box);
    int last_scoring = -score_update_start;
    int scoring_depth = 0;  // the last depth at which we did compute the score
    do {
        DREAL_LOG_INFO << "scoring_icp::solve - loop"
                       << "\t"
                       << "box stack Size = " << box_stack.size();
        double const prec = cs.m_config.nra_delta_test ? 0.0 : cs.m_config.nra_precision;
        tuple<int, box> const branch = box_stack.top();
        box_stack.pop();
        int depth = get<0>(branch);
        cs.m_box = get<1>(branch);
        safe_prune(-1);
        last_scoring++;
        if (!cs.m_box.is_empty()) {
            if (last_scoring < 0                                    // at the start
                || last_scoring >= score_update_period              // periodically recompute
                || depth <= scoring_depth - backtrack_threshold) {  // recompute after backtrack
                prune_split_fixed_point();
                compute_scores();
                last_scoring = std::min(last_scoring, 0);
                scoring_depth = depth;
                if (cs.m_box.is_empty()) {
                    continue;
                }
            }

            int split = -1;
            if (scoring_vs_brancher <= 0 || last_scoring % scoring_vs_brancher == 0) {
                split = highest_score();
            }

            if (split < 0) {
                vector<int> const sorted_dims =
                    brancher.sort_branches(cs.m_box, ctrs, ctc.get_input(), cs.m_config, 1);
                if (sorted_dims.size() > 0) {
                    split = sorted_dims[0];
                }
            }
            if (split >= 0) {
                tuple<int, box, box> splits = cs.m_box.bisect_at(split);
                if (cs.m_config.nra_use_stat) {
                    cs.m_config.nra_stat.increase_branch();
                }
                DREAL_LOG_INFO << "[branched on " << cs.m_box.get_name(split) << "]" << endl;
                box const & first = get<1>(splits);
                box const & second = get<2>(splits);
                int d1 = depth + 1;
                if (second.is_bisectable(prec)) {
                    box_stack.emplace(d1, second);
                    box_stack.emplace(d1, first);
                } else {
                    box_stack.emplace(d1, first);
                    box_stack.emplace(d1, second);
                }
                if (cs.m_config.nra_proof) {
                    cs.m_config.nra_proof_out << "[branched on " << cs.m_box.get_name(split) << "]"
                                              << endl;
                }
            } else {
                for (unsigned i = 0; i < size; i++) {
                    assert(!cs.m_box.is_bisectable_at(i, cs.m_config.nra_precision));
                }
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
    } while (box_stack.size() > 0);

    if (cs.m_config.nra_multiple_soln > 1 && solns.size() > 0) {
        cs.m_box = solns.back();
        return;
    } else {
        assert(!cs.m_box.is_empty() || box_stack.size() == 0);
        return;
    }
}

scoring_icp::scoring_icp(contractor & _ctc, contractor_status & _cs,
                         scoped_vec<shared_ptr<constraint>> const & _ctrs,
                         BranchHeuristic & _brancher)
    : ctc(_ctc),
      cs(_cs),
      brancher(_brancher),
      ctrs(_ctrs),
      solns(),
      box_stack(),
      size(_cs.m_box.size()),
      scores(new double[_cs.m_box.size()]),
      prune_results(new double[_cs.m_box.size()]),
      nbr_prune(new unsigned int[_cs.m_box.size()]) {
    reset_scores();
}

scoring_icp::~scoring_icp() {
    delete[] scores;
    delete[] prune_results;
    delete[] nbr_prune;
}

void scoring_icp::solve(contractor & ctc, contractor_status & cs,
                        scoped_vec<shared_ptr<constraint>> const & ctrs,
                        BranchHeuristic & brancher) {
    scoring_icp icp(ctc, cs, ctrs, brancher);
    icp.solve();
}

}  // namespace dreal
