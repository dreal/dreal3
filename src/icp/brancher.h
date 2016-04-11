/*********************************************************************
Author: Calvin Huang <c@lvin.me>

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

#include <vector>
#include <memory>
#include "util/scoped_vec.h"
#include "util/box.h"
#include "contractor/contractor.h"
using std::shared_ptr;
using std::vector;

namespace dreal {
class BranchHeuristic {
public:
    vector<int> sort_branches(box const &, double) const;
    virtual vector<double> score_axes(box const & b) const = 0;
};

class SizeBrancher: public BranchHeuristic {
public:
    vector<double> score_axes(box const & b) const;
};

class SizeGradAsinhBrancher: public BranchHeuristic {
public:
    explicit SizeGradAsinhBrancher(scoped_vec<shared_ptr<constraint>>& constraints, double c1 = 1000, double c2 = 1000, double c3 = 0.01)
        : constraints(constraints), c1(c1), c2(c2), c3(c3) {}
    vector<double> score_axes(box const & b) const;
private:
    const scoped_vec<shared_ptr<constraint>> constraints;
    const double c1;
    const double c2;
    const double c3;
};
}  // namespace dreal
