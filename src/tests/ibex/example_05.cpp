/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

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

#include <iostream>
#include "ibex/ibex.h"
#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

using ibex::Variable;
using ibex::Function;
using ibex::NumConstraint;
using ibex::CtcFwdBwd;
using ibex::IntervalVector;
using ibex::Interval;
using ibex::ExprSymbol;
using ibex::ExprCtr;
using ibex::ExprConstant;
using ibex::ExprNode;
using std::cout;
using std::endl;

TEST_CASE("ctc_fwdbwd_empty") {
    NumConstraint c("x1", "x2", "x2 < 0");
    IntervalVector box(2);
    box[0] = Interval(0, 0);
    box[1] = Interval(1.5, 1.5);
    cout << "box before=" << box << endl;
    CtcFwdBwd(c).contract(box);
    cout << "box after=" << box << endl;
    REQUIRE(box.is_empty() == 1);
}
