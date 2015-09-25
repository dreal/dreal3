/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include <iostream>
#include <vector>
#include "opensmt/api/OpenSMTContext.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/egraph/Egraph.h"
#include "util/box.h"
#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

using std::cerr;
using std::endl;
using std::vector;

namespace dreal {

TEST_CASE("Create a box") {
    auto context = OpenSMTContext();
    Snode * real_sort = context.mkSortReal();
    context.DeclareFun("x", real_sort);
    context.DeclareFun("y", real_sort);
    context.DeclareFun("z", real_sort);

    auto x = context.mkVar("x");
    auto y = context.mkVar("y");
    auto z = context.mkVar("z");
    x->setDomainLowerBound(3);
    x->setDomainUpperBound(5);
    vector<Enode *> vars {x, y, z};
    box b1(vars);
    cerr << b1 << endl;
    REQUIRE(b1[x].lb() == 3);
    REQUIRE(b1[x].ub() == 5);
}
}  // namespace dreal
