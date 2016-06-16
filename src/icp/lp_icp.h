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

#include "icp/icp.h"
#include "icp/brancher.h"
#include "util/box.h"
#include "util/scoped_vec.h"
#include "contractor/contractor.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/glpk_wrapper.h"

namespace dreal {

class lp_icp {
private:
    static BranchHeuristic & defaultHeuristic;
    static bool is_lp_sat(glpk_wrapper & lp, box & solution, SMTConfig const & config);
public:
    // TODO(damien): the contractor contains both the linear and nonlinear constraints but it only needs the nonlinear ...
    static box solve(box b, contractor & ctc,
            scoped_vec<std::shared_ptr<constraint>>& constraints,
            SMTConfig & config,
            BranchHeuristic & heuristic = defaultHeuristic);
};

}  // namespace dreal
