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

#pragma once

#include <random>
#include <vector>
#include "icp/brancher.h"
#include "util/box.h"
#include "util/scoped_vec.h"
#include "util/stat.h"
#include "contractor/contractor.h"
#include "opensmt/smtsolvers/SMTConfig.h"

namespace dreal {
void output_solution(box const & b, SMTConfig & config, unsigned i = 0);

class naive_icp {
public:
    static box solve(box b, contractor & ctc, SMTConfig & config, scoped_vec<std::shared_ptr<constraint>> stack);
};

class multiheuristic_icp {
public:
    multiheuristic_icp(contractor & ctc, SMTConfig & config, std::vector<std::reference_wrapper<BranchHeuristic>> heuristics) :
        m_ctc(ctc), m_config(config), m_heuristics(heuristics) {};
    box solve(box b, scoped_vec<std::shared_ptr<constraint>> stack);
private:
    void dothread(box & b, BranchHeuristic & heuristic, scoped_vec<std::shared_ptr<constraint>> constraints);
    const contractor & m_ctc;
    SMTConfig & m_config;
    const std::vector<std::reference_wrapper<BranchHeuristic>> m_heuristics;

    std::vector<box> solns;
    std::mutex hulllock;
    std::mutex solutionlock;
    bool solved;
};

class ncbt_icp {
public:
    static box solve(box b, contractor & ctc, SMTConfig & config);
};

class random_icp {
private:
    contractor & m_ctc;
    SMTConfig & m_config;
    std::mt19937_64 m_rg;
    std::uniform_real_distribution<double> m_dist;
    inline bool random_bool() {
        return m_dist(m_rg) >= 0.5;
    }

public:
    random_icp(contractor & ctc, SMTConfig & config);
    box solve(box b, double const precision);
};

}  // namespace dreal
