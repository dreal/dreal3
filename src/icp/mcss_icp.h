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

#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "icp/brancher.h"
#include "util/scoped_vec.h"

namespace dreal {
class BranchHeuristic;
class constraint;
class contractor;
class contractor_status;
template <typename T>
class scoped_vec;

class mcss_icp {
private:
    static BranchHeuristic & defaultHeuristic;

public:
    static void solve(contractor & ctc, contractor_status & cs,
                      scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                      BranchHeuristic & heuristic = defaultHeuristic);
};
}  // namespace dreal
