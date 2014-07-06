/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include <cmath>
#include <iostream>
#include <sstream>
#include <limits>
#include "realpaver/realpaver.h"
#include "gtest/gtest.h"

using std::cout;
using std::cerr;
using std::endl;
using std::stringstream;
using std::numeric_limits;

double inf = numeric_limits<double>::infinity();

#define ASSERT_INTERVAL(i, l, u) ASSERT_TRUE(rp_binf(i) == l); ASSERT_TRUE(rp_bsup(i) == u)

void mul_test(rp_interval result, double i1_lb, double i1_ub, double i2_lb, double i2_ub) {
    static rp_interval i1;
    static rp_interval i2;
    rp_interval_set(i1, i1_lb, i1_ub);
    rp_interval_set(i2, i2_lb, i2_ub);
    rp_interval_mul(result, i1, i2);
    rp_interval_display_simple(i1);
    fprintf(stderr, " * ");
    rp_interval_display_simple(i2);
    fprintf(stderr, " = ");
    rp_interval_display_simple_nl(result);
}

TEST(interval, mul1) {
    // [-oo, oo] * [-oo, oo] = [-oo, oo]
    rp_interval i;
    mul_test(i, -inf, inf, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
    mul_test(i, -inf, inf, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
}

TEST(interval, mul2) {
    // oo * [-oo, oo] = [-oo, oo]
    rp_interval i;
    mul_test(i, inf, inf, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
    mul_test(i, -inf, inf, inf, inf);
}

TEST(interval, mul3) {
    // -oo * [-oo, oo] = [-oo, oo]
    rp_interval i;
    mul_test(i, -inf, -inf, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
    mul_test(i, -inf, inf, -inf, -inf);
    ASSERT_INTERVAL(i, -inf, inf);
}

TEST(interval, mul4) {
    // [0, oo] * [-oo, oo] = [-oo, oo]
    rp_interval i;
    mul_test(i, 0, inf, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
    mul_test(i, -inf, inf, 0, inf);
    ASSERT_INTERVAL(i, -inf, inf);
}

TEST(interval, mul5) {
    // [-oo, 0] * [-oo, oo] = [-oo, oo]
    rp_interval i;
    mul_test(i, -inf, 0, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
    mul_test(i, 0, inf, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
}

TEST(interval, mul6) {
    // [-oo, 0] * [-oo, 0] = [0, +oo]
    rp_interval i;
    mul_test(i, -inf, 0, -inf, 0);
    ASSERT_INTERVAL(i, 0, inf);
}

TEST(interval, mul7) {
    // [-oo, 0] * [0, +oo] = [-oo, 0]
    rp_interval i;
    mul_test(i, -inf, 0, 0, inf);
    ASSERT_INTERVAL(i, -inf, 0);
    mul_test(i, 0, +inf, -inf, 0);
    ASSERT_INTERVAL(i, -inf, 0);
}

TEST(interval, mul10) {
    // [-1, 1] * [-oo, oo] = [-oo, oo]
    rp_interval i;
    mul_test(i, -1, 1, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
    mul_test(i, -inf, inf, -1, 1);
    ASSERT_INTERVAL(i, -inf, inf);
}

TEST(interval, mul11) {
    // [1, 2] * [-oo, oo] = [-oo, oo]
    rp_interval i;
    mul_test(i, -1, 1, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
    mul_test(i, -inf, inf, -1, 1);
    ASSERT_INTERVAL(i, -inf, inf);
}

TEST(interval, mul12) {
    // [-2, -1] * [-oo, oo] = [-oo, oo]
    rp_interval i;
    mul_test(i, -1, 1, -inf, inf);
    ASSERT_INTERVAL(i, -inf, inf);
    mul_test(i, -inf, inf, -1, 1);
    ASSERT_INTERVAL(i, -inf, inf);
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    rp_init_library();
    return RUN_ALL_TESTS();
}
