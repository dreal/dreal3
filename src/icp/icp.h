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

#pragma once

#include <memory>
#include <random>
#include <set>
#include <unordered_map>
#include <vector>

#include "contractor/contractor.h"
#include "icp/brancher.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/scoped_vec.h"
#include "util/stat.h"

struct SMTConfig;

namespace dreal {
class BranchHeuristic;
class box;
class constraint;
class contractor;
class contractor_status;
template <typename T>
class scoped_vec;

void output_solution(box const & b, SMTConfig & config, unsigned i = 0);

class naive_icp {
private:
    static BranchHeuristic & defaultHeuristic;

public:
    static void solve(contractor & ctc, contractor_status & cs,
                      scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                      BranchHeuristic & heuristic = defaultHeuristic);
};

class multiprune_icp {
public:
    static void solve(contractor & ctc, contractor_status & cs,
                      scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                      BranchHeuristic & heuristic, unsigned num_try = 3);
};

class multiheuristic_icp {
public:
    static void solve(contractor & ctc, contractor_status & cs,
                      scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                      std::vector<std::reference_wrapper<BranchHeuristic>> heuristics);
};

class ncbt_icp {
public:
    static void solve(contractor & ctc, contractor_status & cs);
};

class random_icp {
private:
    contractor & m_ctc;
    std::mt19937_64 m_rg;
    std::uniform_real_distribution<double> m_dist;
    inline bool random_bool() { return m_dist(m_rg) >= 0.5; }

public:
    random_icp(contractor & ctc, std::mt19937_64::result_type const random_seed);
    void solve(contractor_status & cs, double const precision);
};

class mcts_icp {
private:
    static BranchHeuristic & defaultHeuristic;

public:
    static void solve(contractor & ctc, contractor_status & cs,
                      scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                      BranchHeuristic & heuristic = defaultHeuristic);
};
}  // namespace dreal
