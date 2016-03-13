/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>
        Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include "api/dreal.hh"
#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch/catch.hpp"

using std::cout;
using std::endl;
using namespace dreal;

TEST_CASE("basic1") {
    solver s;
    expr x = s.var("x", Real);
    expr zero = s.num(0.0);
    expr sn = sin(x);
    expr phi = (sn == zero);
    expr f = x + x * x + sin(x * sin(x));
    expr phi2 = (-f == 0);
    s.add(phi);
    s.add(phi2);
    REQUIRE(s.check());
}

TEST_CASE("basic2") {
    solver s;
    expr    x = s.var("x");
    expr    y = s.var("y");
    expr    phi = x > sin(y);
    expr    psi = y < pow(x, 2);
    expr    psi2 = (x ^ y) > y;
    expr    phi2 = (phi && psi || psi2);
    s.add(phi);
    s.add(phi2);
    s.add(psi2);
    cout << phi2 << endl;
    REQUIRE(s.check());
}
