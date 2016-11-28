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

#pragma once
#include <memory>
#include <stack>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "./dreal_config.h"
#include "contractor/contractor.h"
#include "contractor/contractor_exception.h"
#include "icp/brancher.h"
#include "icp/icp.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/scoped_vec.h"

// can we make that fit into the BranchHeuristic
namespace dreal {
class BranchHeuristic;
class constraint;
class contractor;
class contractor_status;
template <typename T>
class scoped_vec;

class scoring_icp {
private:
    static BranchHeuristic & defaultHeuristic;

    contractor & ctc;
    contractor_status & cs;
    BranchHeuristic & brancher;
    scoped_vec<std::shared_ptr<constraint>> const & ctrs;

    std::vector<box> solns;
    std::stack<std::tuple<int, box>> box_stack;

    unsigned int size;
    double * scores;
    double * prune_results;
    unsigned int * nbr_prune;

    void reset_scores();
    void compute_scores();
    int highest_score();

    double measure(box const & o, box const & n);

    void safe_prune(int idx);
    void prune_split_fixed_point();

    // A bunch of magic constants for the scoring heuristic.
    // Eventually, these should become options.

    static int constexpr score_update_start = 10;
    static int constexpr score_update_period = 10;
    static double constexpr score_update_old_weight = 0.5;
    static double constexpr progress_threshold = 0.9;
    static int constexpr backtrack_threshold = 10;
    static int constexpr scoring_vs_brancher = 0;

    void solve();

public:
    scoring_icp(contractor & ctc, contractor_status & cs,
                scoped_vec<std::shared_ptr<constraint>> const & ctrs, BranchHeuristic & heuristic);
    ~scoring_icp();

    static void solve(contractor & ctc, contractor_status & cs,
                      scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                      BranchHeuristic & heuristic = defaultHeuristic);
};
}  // namespace dreal
