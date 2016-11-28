/*********************************************************************
Author: Calvin Huang <c@lvin.me>
        Soonho Kong  <soonhok@cs.cmu.edu>

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

#include <limits>
#include <memory>
#include <vector>

#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "ibex_BitSet.h"
#include "util/box.h"
#include "util/scoped_vec.h"

struct SMTConfig;

namespace dreal {
class box;
class constraint;
template <typename T>
class scoped_vec;

class BranchHeuristic {
public:
    std::vector<int> sort_branches(box const &,
                                   scoped_vec<std::shared_ptr<constraint>> const & ctrs,
                                   ibex::BitSet const & intput, SMTConfig const & config,
                                   int num_try) const;
    virtual std::vector<double> score_axes(box const & b) const = 0;
};

class SizeBrancher : public BranchHeuristic {
public:
    std::vector<double> score_axes(box const & b) const;
};

class SizeGradAsinhBrancher : public BranchHeuristic {
public:
    explicit SizeGradAsinhBrancher(scoped_vec<std::shared_ptr<constraint>> const & constraints,
                                   double const c1 = 1000, double const c2 = 1000,
                                   double const c3 = 0.01)
        : constraints(constraints), c1(c1), c2(c2), c3(c3) {}
    std::vector<double> score_axes(box const & b) const;

private:
    scoped_vec<std::shared_ptr<constraint>> const & constraints;
    const double c1;
    const double c2;
    const double c3;
};
}  // namespace dreal
