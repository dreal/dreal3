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

#pragma once

#include <memory>
#include <unordered_set>

#include "./dreal_config.h"
#include "contractor/contractor.h"
#include "icp/brancher.h"
#include "icp/icp.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/glpk_wrapper.h"
#include "util/scoped_vec.h"

class Enode;
namespace dreal {
class BranchHeuristic;
class box;
class constraint;
class contractor;
class contractor_status;
class glpk_wrapper;
template <typename T>
class scoped_vec;
}  // namespace dreal
struct SMTConfig;

#ifdef USE_GLPK
namespace dreal {
class lp_icp {
private:
    static BranchHeuristic & defaultHeuristic;
    static void mark_basic(glpk_wrapper & lp, std::unordered_set<Enode *> es,
                           scoped_vec<std::shared_ptr<constraint>> & constraints,
                           std::unordered_set<std::shared_ptr<constraint>> & used_constraints);
    static bool is_lp_sat(glpk_wrapper & lp, box & solution, SMTConfig const & config);
    static void prune(glpk_wrapper & lp, int i, box & solution, SMTConfig const & config);

public:
    // TODO(damien): the contractor contains both the linear and nonlinear constraints but it only
    // needs the nonlinear ...
    static void solve(contractor & ctc, contractor_status & cs,
                      scoped_vec<std::shared_ptr<constraint>> & constraints,
                      BranchHeuristic & heuristic = defaultHeuristic);
};
}  // namespace dreal
#endif  // #ifdef USE_GLPK
