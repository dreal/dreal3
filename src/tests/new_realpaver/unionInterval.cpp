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

#include <iostream>
#include "new_realpaver/interval.h"
#include "new_realpaver/unionInterval.h"
#include "gtest/gtest.h"

using namespace realpaver;
using std::cout;
using std::endl;

TEST(unionInterval, 1) {
    unionInterval u1(interval(0.0, 3.14));
}

TEST(unionInterval, 2) {
    unionInterval u1({interval(0.0, 3.14)});
}

TEST(constructor, 1) {
    unionInterval u1({interval(0.0, 3.14)});
    unionInterval u2(interval(0.0, 3.14));
    ASSERT_TRUE(u1 == u2);
}
TEST(constructor, 2) {
    interval const & empty = interval::empty;
    unionInterval u1({empty});
    unionInterval u2(empty);
    ASSERT_TRUE(u1 == u2);
}

TEST(hull, 1) {
    unionInterval u1({interval(0.0, 3.14)});
    unionInterval u2(interval(0.0, 3.14));
    ASSERT_TRUE(u1.hull() == interval(0.0, 3.14));
    ASSERT_TRUE(u2.hull() == interval(0.0, 3.14));
}

TEST(hull, 2) {
    unionInterval u;
    ASSERT_TRUE(u.hull() == interval::empty);
}

TEST(hull, 3) {
    unionInterval u1({{0.0, 3.14}, {2.0, 3.15}, {6.0, 9.15}, {-34.0, 1.5}, {345, 9873.14} });
    unionInterval u2({{-34.0, 3.15}, {6.0, 9.15}, {345, 9873.14}});
    ASSERT_TRUE(u1.hull() == interval(-34.0, 9873.14));
}

TEST(insert, 1) {
    unionInterval u1({{0.0, 3.14}, {2.0, 3.15}, {6.0, 9.15}, {-34.0, 1.5}, {345, 9873.14} });
    unionInterval u2({{-34.0, 3.15}, {6.0, 9.15}, {345, 9873.14}});
    ASSERT_TRUE(u1 == u2);
}
TEST(insert, 2) {
    unionInterval u1({{0, 1}, {2, 3}, {4, 5}, {6, 7}});
    unionInterval u2({{1, 2}, {3, 4}, {5, 6}, {7, 8}});
    ASSERT_EQ(u1.size(), static_cast<unsigned>(4));
    ASSERT_EQ(u2.size(), static_cast<unsigned>(4));
    ASSERT_TRUE(u1.hull() == interval(0, 7));
    ASSERT_TRUE(u2.hull() == interval(1, 8));
    u2.insert(u1);
    ASSERT_EQ(u2.size(), static_cast<unsigned>(1));
    ASSERT_TRUE(u2 == unionInterval(interval(0, 8)));
}

TEST(insert, 3) {
    unionInterval u1({{345, 9873.14}, {-34.0, 1.5}, {6.0, 9.15}, {2.0, 3.15}, {0.0, 3.14}});
    unionInterval u2({{0.0, 3.14}, {2.0, 3.15}, {6.0, 9.15}, {-34.0, 1.5}, {345, 9873.14} });
    ASSERT_TRUE(u1 == u2);
}

TEST(size, 1) {
    unionInterval u1;
    unionInterval u2({});
    unionInterval u3({interval::empty});
    unionInterval u4({interval::empty, interval::empty, interval::empty});
    ASSERT_EQ(u1.size(), 0);
    ASSERT_EQ(u2.size(), 0);
    ASSERT_EQ(u3.size(), 0);
    ASSERT_EQ(u4.size(), 0);
}

TEST(size, 2) {
    unionInterval u1({interval()});
    unionInterval u2({interval(), interval::empty});
    unionInterval u3({interval::empty, interval()});
    unionInterval u4({{0, 0}, {1, 1}});
    unionInterval u5({{0, 0}, {1, 1}, interval::realline});
    ASSERT_EQ(u1.size(), 1);
    ASSERT_EQ(u2.size(), 1);
    ASSERT_EQ(u3.size(), 1);
    ASSERT_EQ(u4.size(), 2);
    ASSERT_EQ(u5.size(), 1);
}


int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    interval::init();
    return RUN_ALL_TESTS();
    return 0;
}
