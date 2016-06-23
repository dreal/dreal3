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

#include <iostream>
#include "ibex/ibex.h"
#include "util/ibex_enode.h"
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
using std::cerr;
using std::endl;
using dreal::str_to_ibex_interval;

TEST_CASE("rounding_1") {
    NumConstraint c("x", "y", "z", "x = y + z");
    IntervalVector box(3);
    box[0] = Interval(nextafter(0.7, 0), nextafter(0.7, 1));
    box[1] = Interval(nextafter(0.6353, 0), nextafter(0.6353, 1));
    box[2] = Interval(nextafter(0.0647, 0), nextafter(0.0647, 1));
    cerr << "box before=" << box << endl;
    CtcFwdBwd(c).contract(box);
    cerr << "box after=" << box << endl;
    REQUIRE(box.is_empty() == 0);
}

TEST_CASE("rounding_2") {
    NumConstraint c("x", "y", "z", "x = y + z");
    IntervalVector box(3);
    box[0] = Interval(7) / Interval(10);
    box[1] = Interval(6353) / Interval(10000);
    box[2] = Interval(647) / Interval(10000);
    cerr << "box before=" << box << endl;
    CtcFwdBwd(c).contract(box);
    cerr << "box after=" << box << endl;
    REQUIRE(box.is_empty() == 0);
}

TEST_CASE("rounding_3") {
    NumConstraint c("x", "y", "z", "x - y = z");
    IntervalVector box(3);
    box[0] = str_to_ibex_interval("0.7");
    box[1] = str_to_ibex_interval("0.6353");
    box[2] = str_to_ibex_interval("0.0647");
    cerr << "box before=" << box << endl;
    CtcFwdBwd(c).contract(box);
    cerr << "box after=" << box << endl;
    REQUIRE(box.is_empty() == 0);  // FAIL
}

TEST_CASE("rounding_4") {
    NumConstraint c1("x", "y", "z", "w", "x - y - z = 0");
    NumConstraint c2("x", "y", "z", "w", "z - w = 0");
    IntervalVector box(4);
    box[0] = str_to_ibex_interval("0.7");     // x
    box[1] = str_to_ibex_interval("0.6353");  // y
    box[2] = ibex::Interval(0, 10);           // z
    box[3] = str_to_ibex_interval("0.0647");  // w
    cerr << "box before =" << box << endl;
    CtcFwdBwd(c1).contract(box);
    cerr << "after c1   =" << box << endl;
    CtcFwdBwd(c2).contract(box);
    cerr << "after c2   =" << box << endl;
    REQUIRE(box.is_empty() == 0);  // FAIL
}

TEST_CASE("rounding_5") {
    NumConstraint c1("p_0", "p_t", "t_0", "t_t", "time", "p_t - (p_0 + time) = 0");
    NumConstraint c2("p_0", "p_t", "t_0", "t_t", "time", "t_t - (t_0 + time) = 0");
    IntervalVector box(5);
    box[0] = str_to_ibex_interval("0.6353");     // p_0
    box[1] = str_to_ibex_interval("0.7");        // p_t
    box[2] = str_to_ibex_interval("0");          // t_0
    box[3] = str_to_ibex_interval("0.0647");     // t_t
    box[4] = ibex::Interval(0, 10);              // time
    cerr.precision(16);
    cerr << "init box:\n" << box << endl;
    CtcFwdBwd(c1).contract(box);
    cerr << "after c1\n" << box << endl;
    CtcFwdBwd(c2).contract(box);
    cerr << "after c2\n" << box << endl;
    REQUIRE(box.is_empty() == 0);  // FAIL
}

TEST_CASE("rounding_6") {
    auto iv1 = Interval(647) / Interval(10000);
    auto iv2 = str_to_ibex_interval("0.0647");
    cerr << "iv1.diam() = " << iv1.diam() << std::endl;
    cerr << "iv2.diam() = " << iv2.diam() << std::endl;
    REQUIRE(iv1.diam() == iv2.diam());
}
