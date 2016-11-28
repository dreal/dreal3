/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>
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

#include <iostream>
#include <string>

#include "api/dreal.h"

#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

using std::cout;
using std::endl;
using std::stringstream;
using dreal::solver;
using dreal::expr;
using dreal::vtype;

TEST_CASE("basic1") {
    solver s;
    expr const x = s.var("x", vtype::Real);
    expr const zero = s.num(0.0);
    expr const sn = sin(x);
    expr const phi = (sn == zero);
    expr const f = x + x * x + sin(x * sin(x));
    expr const phi2 = (-f == 0);
    s.add(phi);
    s.add(phi2);
    REQUIRE(s.check());
}

TEST_CASE("basic2") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const phi = x > sin(y);
    expr const psi = y < pow(x, 2);
    expr const psi2 = (x ^ 2) > y;
    expr const phi2 = ((phi && psi) || psi2);
    s.add(phi);
    s.add(phi2);
    s.add(psi2);
    stringstream ss;
    ss << phi2;
    REQUIRE(ss.str() ==
            "(or (and (not (<= x (sin y))) (not (<= (^ x 2) y))) (not (<= (^ x 2) y)))");
    REQUIRE(s.check());
}

TEST_CASE("basic3") {
    solver s;
    expr const x = s.var("x");
    expr const phi = (x + x + x) == 0;
    s.add(phi);
    cout << phi << endl;
    REQUIRE(s.check());
}

TEST_CASE("operator+") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const z = s.var("z");
    expr const phi = (x + y + z);
    stringstream ss;
    ss << phi;
    REQUIRE(ss.str() == "(+ (+ x y) z)");
}

TEST_CASE("operator-") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const z = s.var("z");
    expr const phi = (x - y - z);
    stringstream ss;
    ss << phi;
    REQUIRE(ss.str() == "(+ (+ x (* -1 y)) (* -1 z))");  // (x + (-y)) + (-z)
}

TEST_CASE("operator*") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const z = s.var("z");
    expr const phi = (x * y * z);
    stringstream ss;
    ss << phi;
    REQUIRE(ss.str() == "(* (* x y) z)");
}

TEST_CASE("operator/") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const z = s.var("z");
    expr const phi = (x / y / z);
    stringstream ss;
    ss << phi;
    REQUIRE(ss.str() == "(/ (/ x y) z)");
}

TEST_CASE("operator>") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const phi = x > y;
    stringstream ss;
    ss << phi;
    REQUIRE(ss.str() == "(not (<= x y))");
}

TEST_CASE("operator>=") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const phi = x >= y;
    stringstream ss;
    ss << phi;
    REQUIRE(ss.str() == "(<= y x)");
}

TEST_CASE("operator<") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const phi = x < y;
    stringstream ss;
    ss << phi;
    REQUIRE(ss.str() == "(not (<= y x))");  // that is, y > x
}

TEST_CASE("operator<=") {
    solver s;
    expr const x = s.var("x");
    expr const y = s.var("y");
    expr const phi = x <= y;
    stringstream ss;
    ss << phi;
    REQUIRE(ss.str() == "(<= x y)");
}
