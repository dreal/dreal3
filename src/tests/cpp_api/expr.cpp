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

#include <cassert>
#include <iostream>
#include <sstream>
#include <vector>
#include "api/dreal.hh"

#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

using dreal::solver;
using dreal::expr;
using std::vector;
using std::ostringstream;
using std::cerr;
using std::endl;

TEST_CASE("x < y") {
    solver s;
    expr x = s.var("x", -5, 5);
    expr y = s.var("y", -5, 5);
    ostringstream ss;
    ss << (x < y);
    REQUIRE(ss.str() == "(not (<= y x))");
}

TEST_CASE("x > y") {
    solver s;
    expr x = s.var("x", -5, 5);
    expr y = s.var("y", -5, 5);
    ostringstream ss;
    ss << (x > y);
    REQUIRE(ss.str() == "(not (<= x y))");
}

TEST_CASE("x <= y") {
    solver s;
    expr x = s.var("x", -5, 5);
    expr y = s.var("y", -5, 5);
    ostringstream ss;
    ss << (x <= y);
    REQUIRE(ss.str() == "(<= x y)");
}

TEST_CASE("x >= y") {
    solver s;
    expr x = s.var("x", -5, 5);
    expr y = s.var("y", -5, 5);
    ostringstream ss;
    ss << (x >= y);
    REQUIRE(ss.str() == "(<= y x)");
}

TEST_CASE("x == y") {
    solver s;
    expr x = s.var("x", -5, 5);
    expr y = s.var("y", -5, 5);
    ostringstream ss;
    ss << (x == y);
    REQUIRE(ss.str() == "(= x y)");
}

TEST_CASE("!(x == y)") {
    solver s;
    expr x = s.var("x", -5, 5);
    expr y = s.var("y", -5, 5);
    ostringstream ss;
    ss << !(x == y);
    REQUIRE(ss.str() == "(not (= x y))");
}

TEST_CASE("x < 1") {
    solver s;
    expr x = s.var("x", -5, 5);
    ostringstream ss;
    ss << (x < 1);
    REQUIRE(ss.str() == "(not (<= 1 x))");
}

TEST_CASE("1 < x") {
    solver s;
    expr x = s.var("x", -5, 5);
    ostringstream ss;
    ss << (1 < x);
    REQUIRE(ss.str() == "(not (<= x 1))");
}

TEST_CASE("x <= 1") {
    solver s;
    expr x = s.var("x", -5, 5);
    ostringstream ss;
    ss << (x <= 1);
    REQUIRE(ss.str() == "(<= x 1)");
}

TEST_CASE("1 <= x") {
    solver s;
    expr x = s.var("x", -5, 5);
    ostringstream ss;
    ss << (1 <= x);
    REQUIRE(ss.str() == "(<= 1 x)");
}

TEST_CASE("x > 1") {
    solver s;
    expr x = s.var("x", -5, 5);
    ostringstream ss;
    ss << (x > 1);
    REQUIRE(ss.str() == "(not (<= x 1))");
}

TEST_CASE("1 > x") {
    solver s;
    expr x = s.var("x", -5, 5);
    ostringstream ss;
    ss << (1 > x);
    REQUIRE(ss.str() == "(not (<= 1 x))");
}

TEST_CASE("x >= 1") {
    solver s;
    expr x = s.var("x", -5, 5);
    ostringstream ss;
    ss << (x >= 1);
    REQUIRE(ss.str() == "(<= 1 x)");
}

TEST_CASE("1 >= x") {
    solver s;
    expr x = s.var("x", -5, 5);
    ostringstream ss;
    ss << (1 >= x);
    REQUIRE(ss.str() == "(<= x 1)");
}
