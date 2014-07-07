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
#include "new_realpaver/interval.h"
#include "gtest/gtest.h"

using namespace realpaver;
using std::cout;
using std::cerr;
using std::endl;
using std::stringstream;
using std::numeric_limits;

TEST(constant, pi) {
    double const pi_low = 3.141592653589793;
    double const pi_high = 3.141592653589794;
    ASSERT_EQ(interval::HALF_PI, asin(1.0));
    ASSERT_LE(pi_low / 2.0,      interval::HALF_PI);
    ASSERT_LE(interval::HALF_PI, pi_high / 2.0);
    ASSERT_LE(pi_low,            interval::PI);
    ASSERT_LE(interval::PI,      pi_high);
}

TEST(constant, other_pis) {
    ASSERT_EQ(interval::HALF_PI_3, interval::HALF_PI * 3);
    ASSERT_EQ(interval::HALF_PI_5, interval::HALF_PI * 5);
    ASSERT_EQ(interval::HALF_PI_7, interval::HALF_PI * 7);
    ASSERT_EQ(interval::PI,        interval::HALF_PI * 2);
    ASSERT_EQ(interval::PI_2,      interval::PI * 2);
    ASSERT_EQ(interval::PI_4,      interval::PI * 4);
}

TEST(constant, empty_real) {
    ASSERT_TRUE(interval::empty.isEmpty());
    ASSERT_FALSE(interval::empty.isRealline());
    ASSERT_TRUE(interval::realline.isRealline());
    ASSERT_FALSE(interval::realline.isEmpty());
    ASSERT_EQ(interval::realline.inf, -numeric_limits<double>::infinity());
    ASSERT_EQ(interval::realline.sup, +numeric_limits<double>::infinity());
}

TEST(constructor, empty) {
    interval const i;
    ASSERT_EQ(i.inf, -numeric_limits<double>::infinity());
    ASSERT_EQ(i.sup, +numeric_limits<double>::infinity());
}

TEST(constructor, point) {
    interval const i(3.0);
    ASSERT_EQ(i.inf, 3.0);
    ASSERT_EQ(i.sup, 3.0);
    ASSERT_TRUE(i.isPoint());
}

TEST(constructor, two_points) {
    interval const i1(-2387936.2389, 43578934.42309843);
    interval const i2(-43578934.42309843, 2387936.2389);
    ASSERT_EQ(i1.inf, -2387936.2389);
    ASSERT_EQ(i1.sup, 43578934.42309843);
    ASSERT_EQ(i2.inf, -43578934.42309843);
    ASSERT_EQ(i2.sup, 2387936.2389);
}

TEST(constructor, filib) {
    interval const i1(interval::filib_interval(-2387936.2389, 43578934.42309843));
    interval const i2(interval::filib_interval(-43578934.42309843, 2387936.2389));
    ASSERT_EQ(i1.inf, -2387936.2389);
    ASSERT_EQ(i1.sup, 43578934.42309843);
    ASSERT_EQ(i2.inf, -43578934.42309843);
    ASSERT_EQ(i2.sup, 2387936.2389);
}

TEST(constructor, interval) {
    interval const i1(interval::empty);
    interval const i2(interval::realline);
    interval const i3(3.0);
    interval const i4(3.0, 4.0);
    interval const i5(i3);
    interval const i6(i4);
    ASSERT_TRUE(i1 == interval::empty);
    ASSERT_TRUE(i2 == interval::realline);
    ASSERT_TRUE(i3 == i5);
    ASSERT_TRUE(i4 == i6);
    ASSERT_EQ(i5.inf, 3.0);
    ASSERT_EQ(i5.sup, 3.0);
    ASSERT_EQ(i6.inf, 3.0);
    ASSERT_EQ(i6.sup, 4.0);
}

TEST(constructor, string1) {
    interval const i1("34897.2437e+18");
    interval const i2("34897.2437E+18");
    interval const i3("34897.2437e18");
    interval const i4("34897.2437E18");
    ASSERT_TRUE(i1.includes(34897.2437e+18));
    ASSERT_TRUE(i2.includes(34897.2437e+18));
    ASSERT_TRUE(i3.includes(34897.2437e+18));
    ASSERT_TRUE(i4.includes(34897.2437e+18));
}

TEST(constructor, string2) {
    interval const i1("-34897.2437e-18");
    interval const i2("-34897.2437E-18");
    interval const i3("-34897.2437e-18");
    interval const i4("-34897.2437E-18");
    ASSERT_TRUE(i1.includes(-34897.2437e-18));
    ASSERT_TRUE(i2.includes(-34897.2437e-18));
    ASSERT_TRUE(i3.includes(-34897.2437e-18));
    ASSERT_TRUE(i4.includes(-34897.2437e-18));
}

TEST(constructor, string3) {
    interval const i1("0.3127347");
    interval const i2("3.14175");
    interval const i3("-34733.13744");
    interval const i4("-0.374743814");
    interval const i5(".3127347");
    interval const i6("-.374743814");
    ASSERT_TRUE(i1.includes(0.3127347));
    ASSERT_TRUE(i2.includes(3.14175));
    ASSERT_TRUE(i3.includes(-34733.13744));
    ASSERT_TRUE(i4.includes(-0.374743814));
    ASSERT_TRUE(i5.includes(.3127347));
    ASSERT_TRUE(i6.includes(-.374743814));
}
TEST(constructor, string4) {
    interval const i1("0.3127347");
    interval const i2("3.14175");
    interval const i3("-34733.13744");
    interval const i4("-0.374743814");
    interval const i5(".3127347");
    interval const i6("-.374743814");
    ASSERT_TRUE(i1.includes(0.3127347));
    ASSERT_TRUE(i2.includes(3.14175));
    ASSERT_TRUE(i3.includes(-34733.13744));
    ASSERT_TRUE(i4.includes(-0.374743814));
    ASSERT_TRUE(i5.includes(.3127347));
    ASSERT_TRUE(i6.includes(-.374743814));
}

TEST(constructor, string5) {
    ASSERT_TRUE(interval("3.0").includes(3.0));
    ASSERT_TRUE(interval("34").includes(34));
    ASSERT_TRUE(interval("3").includes(3));
    ASSERT_TRUE(interval("356").includes(356));
    ASSERT_TRUE(interval("0.0").includes(0.0));
    ASSERT_TRUE(interval("04").includes(4));
    ASSERT_TRUE(interval("0").includes(0));
    ASSERT_TRUE(interval(".3412").includes(0.3412));
    ASSERT_TRUE(interval("-3.0").includes(-3));
    ASSERT_TRUE(interval("-34").includes(-34));
    ASSERT_TRUE(interval("-3").includes(-3));
    ASSERT_TRUE(interval("-356").includes(-356));
    ASSERT_TRUE(interval("-0.0").includes(-0.0));
    ASSERT_TRUE(interval("-04").includes(-4));
    ASSERT_TRUE(interval("-0").includes(0.0));
    ASSERT_TRUE(interval("-.3412").includes(-0.3412));
    ASSERT_TRUE(interval("-3.0e4").includes(-3.0 * 10000));
    ASSERT_TRUE(interval("-34e2").includes(-34 * 100));
    ASSERT_TRUE(interval("-3e7").includes(-3 * 10000000));
    ASSERT_TRUE(interval("-356e8").includes(-356 * 100000000.0));
    ASSERT_TRUE(interval("-0.0e1").includes(0.0 * 10));
    ASSERT_TRUE(interval("-04e2").includes(-4 * 100));
    ASSERT_TRUE(interval("-0e4").includes(0 * 10000));
    ASSERT_TRUE(interval("-.3412e5").includes(-0.3412 * 100000));
    ASSERT_TRUE(interval("-3.0e-4").includes(-3.0 / 10000.0));
    ASSERT_TRUE(interval("-34e-2").includes(-34 / 100.0));
    ASSERT_TRUE(interval("-3e-7").includes(-3 / 10000000.0));
    ASSERT_TRUE(interval("-356e-8").includes(-356 / 100000000.0));
    ASSERT_TRUE(interval("-0.0e-1").includes(0.0));
    ASSERT_TRUE(interval("-04e-2").includes(-4 / 100.0));
    ASSERT_TRUE(interval("-0e-4").includes(0.0));
    ASSERT_TRUE(interval("-.3412e-5").includes(-0.3412 / 100000.0));
}

TEST(constructor, istream1) {
    stringstream ss;
    ss << "0.3127347 ";
    ss << "3.14175 ";
    ss << "0.25 ";
    interval const i1(ss);
    interval const i2(ss);
    interval const i3("0.3127347");
    interval const i4("3.14175");
    interval const i5(ss);
    interval const i6("0.25");
    ASSERT_TRUE(i1 == i3);
    ASSERT_TRUE(i2 == i4);
    ASSERT_TRUE(i5 == i6);
    ASSERT_FALSE(i1.isPoint());
    ASSERT_FALSE(i2.isPoint());
    ASSERT_FALSE(i3.isPoint());
    ASSERT_FALSE(i4.isPoint());
    ASSERT_TRUE(i5.isPoint());
    ASSERT_TRUE(i6.isPoint());
}

TEST(constructor, istream2) {
    stringstream ss;
    ss << "   [   3.141592  ,    4.08   ]";
    ss << "[   3.141592  ,    4.08   ]";
    ss << "3.141592";
    interval i1;
    interval i2;
    interval i3;
    ss >> i1;
    ss >> i2;
    ss >> i3;
    ASSERT_TRUE(i1.includes(interval(3.141592, 4.08)));
    ASSERT_TRUE(i2.includes(interval(3.141592, 4.08)));
    ASSERT_TRUE(i3.includes(3.141592));
}

TEST(equal_digits, 1) {
    interval const i1(3.0, 4.0);
    interval const i2(i1);
    ASSERT_TRUE(i1.equal_digits(i2, 10));
}

TEST(equal_digits, 2) {
    interval const i1(3.10001, 4.000001);
    interval const i2(3.10002, 4.000002);
    ASSERT_TRUE(i1.equal_digits(i2, 4));
    ASSERT_FALSE(i1.equal_digits(i2, 5));
}

TEST(empty, 1) {
    interval i;
    ASSERT_FALSE(i.isEmpty());
}
TEST(empty, 2) {
    interval i(3.1415, 6.18);
    ASSERT_FALSE(i.isEmpty());
}
TEST(empty, 3) {
    ASSERT_TRUE(interval::empty.isEmpty());
}
TEST(equal_diff, 1) {
    interval i1(-3.5, 4.3);
    interval i2(-2.5, 4.8);
    ASSERT_FALSE(i1.equals(i2));
    ASSERT_FALSE(i1 == i2);
    ASSERT_TRUE(i1.diff(i2));
    ASSERT_TRUE(i1 != i2);
}
TEST(equal_diff, 2) {
    interval i1(-3.5, 4.3);
    interval i2(-2.5, 4.8);
    ASSERT_TRUE(i1.equals(i1));
    ASSERT_TRUE(i1 == i1);
    ASSERT_FALSE(i1.diff(i1));
    ASSERT_FALSE(i1 != i1);
    ASSERT_TRUE(i2.equals(i2));
    ASSERT_TRUE(i2 == i2);
    ASSERT_FALSE(i2.diff(i2));
    ASSERT_FALSE(i2 != i2);
}
TEST(includes, point) {
    interval i(-3.5, 4.3);
    ASSERT_TRUE(i.includes(-2.0));
    ASSERT_TRUE(i.includes(-1.0));
    ASSERT_TRUE(i.includes(1.0));
    ASSERT_TRUE(i.includes(2.0));
    ASSERT_TRUE(includes(i, -2.0));
    ASSERT_TRUE(includes(i, -1.0));
    ASSERT_TRUE(includes(i, 1.0));
    ASSERT_TRUE(includes(i, 2.0));
    ASSERT_FALSE(i.includes(-4.0));
    ASSERT_FALSE(i.includes(-5.0));
    ASSERT_FALSE(i.includes(5.0));
    ASSERT_FALSE(i.includes(6.0));
    ASSERT_FALSE(includes(i, -4.0));
    ASSERT_FALSE(includes(i, -5.0));
    ASSERT_FALSE(includes(i, 5.0));
    ASSERT_FALSE(includes(i, 6.0));
}
TEST(includes, interval1) {
    interval const & real = interval::realline;
    interval const & empty = interval::empty;
    ASSERT_TRUE(real.includes(empty));
    ASSERT_TRUE(includes(real, empty));
}
TEST(includes, interval2) {
    interval const i1(35.1, 58);
    interval const i2(35.1, 36);
    interval const & empty = interval::empty;
    ASSERT_TRUE(i1.includes(empty));
    ASSERT_TRUE(includes(i1, empty));
    ASSERT_TRUE(i2.includes(empty));
    ASSERT_TRUE(includes(i2, empty));
    ASSERT_TRUE(i1.includes(i2));
    ASSERT_TRUE(includes(i1, i2));
    ASSERT_FALSE(i2.includes(i1));
    ASSERT_FALSE(includes(i2, i1));
}
TEST(includes, interval3) {
    interval const i1(35.1, 58);
    interval const i2(33.1, 47);
    interval const & empty = interval::empty;
    ASSERT_TRUE(i1.includes(empty));
    ASSERT_TRUE(includes(i1, empty));
    ASSERT_TRUE(i2.includes(empty));
    ASSERT_TRUE(includes(i2, empty));
    ASSERT_FALSE(i1.includes(i2));
    ASSERT_FALSE(includes(i1, i2));
    ASSERT_FALSE(i2.includes(i1));
    ASSERT_FALSE(includes(i2, i1));
}
TEST(includesStrictly, 1) {
    interval const i(0.0, 2.0);
    ASSERT_TRUE(i.includes(i));
    ASSERT_FALSE(i.includesStrictly(i));
}
TEST(includesStrictly, 2) {
    interval const i;
    ASSERT_TRUE(i.includes(i));
    ASSERT_FALSE(i.includesStrictly(i));
}
TEST(includesStrictly, 3) {
    interval const i(0.0, 2.0);
    ASSERT_TRUE(i.includes(0.5));
    ASSERT_TRUE(i.includes(1.5));
    ASSERT_TRUE(i.includes(0.0));
    ASSERT_TRUE(i.includes(2.0));
    ASSERT_FALSE(i.includes(-0.1));
    ASSERT_FALSE(i.includes(2.1));
    ASSERT_TRUE(i.includesStrictly(0.5));
    ASSERT_TRUE(i.includesStrictly(1.5));
    ASSERT_FALSE(i.includesStrictly(0.0));
    ASSERT_FALSE(i.includesStrictly(2.0));
    ASSERT_FALSE(i.includesStrictly(-0.1));
    ASSERT_FALSE(i.includesStrictly(2.1));
}
TEST(isPoint, 1) {
    interval const i;
    ASSERT_FALSE(i.isPoint());
}
TEST(isPoint, 2) {
    interval const i(3.0, 4.0);
    ASSERT_FALSE(i.isPoint());
}
TEST(isPoint, 3) {
    interval const i(3.0, 3.0);
    ASSERT_TRUE(i.isPoint());
}
TEST(isInt, 1) {
    interval const i(3.0, 3.0);
    ASSERT_TRUE(i.isInt());
}
TEST(isInt, 2) {
    interval const i(2.0, 3.0);
    ASSERT_FALSE(i.isInt());
}
TEST(isZero, 1) {
    interval const i(3.0, 3.0);
    ASSERT_FALSE(i.isZero());
}
TEST(isZero, 2) {
    interval const i(0.0, 0.0);
    ASSERT_TRUE(i.isZero());
}
TEST(isZero, 3) {
    interval const i(-1.0, 2.0);
    ASSERT_FALSE(i.isZero());
}
TEST(isZero, 4) {
    interval const i;
    ASSERT_FALSE(i.isZero());
}
TEST(isZero, 5) {
    interval const & empty = interval::empty;
    ASSERT_FALSE(empty.isZero());
}
TEST(boundZero, 1) {
    interval const i1(0.0, 3.0);
    interval const i2(-3.0, 0.0);
    interval const i3(-3.0, 3.0);
    interval const i4;
    interval const & empty = interval::empty;
    ASSERT_TRUE(i1.boundZero());
    ASSERT_TRUE(i2.boundZero());
    ASSERT_FALSE(i3.boundZero());
    ASSERT_FALSE(i4.boundZero());
    ASSERT_FALSE(empty.boundZero());
}
TEST(disjointWith, 1) {
    interval const i1(0.0, 3.0);
    interval const i2(-3.0, 0.0);
    interval const i3(-3.0, 3.0);
    ASSERT_FALSE(i1.disjointWith(i2));
    ASSERT_FALSE(i1.disjointWith(i3));
    ASSERT_FALSE(i2.disjointWith(i3));
}
TEST(disjointWith, 2) {
    interval const i1(0.00001, 3.0);
    interval const i2(-3.0, -0.000001);
    interval const i3(-3.0, 3.0);
    ASSERT_TRUE(i1.disjointWith(i2));
    ASSERT_TRUE(i2.disjointWith(i1));
    ASSERT_TRUE(disjointWith(i1, i2));
    ASSERT_TRUE(disjointWith(i1, i2));
    ASSERT_FALSE(i1.disjointWith(i3));
    ASSERT_FALSE(i2.disjointWith(i3));
}
TEST(infinite_finite, 1) {
    interval const i1;
    interval i2;
    interval i3;
    i2.sup = 0.0;
    i3.inf = 0.0;
    ASSERT_TRUE(i1.infinite());
    ASSERT_TRUE(i2.infinite());
    ASSERT_TRUE(i3.infinite());
    ASSERT_FALSE(i1.finite());
    ASSERT_FALSE(i2.finite());
    ASSERT_FALSE(i3.finite());
    i2.inf = -10.0;
    i3.sup = 10.0;
    ASSERT_FALSE(i2.infinite());
    ASSERT_FALSE(i3.infinite());
    ASSERT_TRUE(i2.finite());
    ASSERT_TRUE(i3.finite());
}
TEST(width, 1) {
    interval const real;
    ASSERT_EQ(real.width(), +interval::DBL_INFINITY);
}
TEST(width, 2) {
    interval const i(0.0, 1.0);
    ASSERT_EQ(i.width(), 1.0);
}
TEST(midpoint, 1) {
    interval const i;
    ASSERT_EQ(i.midpoint(), 0);
}
TEST(midpoint, 2) {
    interval const i;
    ASSERT_EQ(i.midpoint(), 0);
}

TEST(add, 1) {
    interval const i1(0.0, 3.0);
    interval i2 = i1 + interval::empty;
    ASSERT_TRUE(i2 == interval::empty);
}

TEST(tra, 1) {
    // 0.72061401054487106421220232732594013214111328125,
    // 1.10569445613736194744833247306771509923367712439402389679177218795302906073629856109619140625e-17,
    // 0.69333646075079335968638361009652726352214813232421875,
    // 1.28228316745299687455707879457586503804308336679977468886004743353623780421912670135498046875e-17,

    interval const   x(0.84375, 0.8437500000000001);
    interval const  sn(0.7206140105448698, 0.7206140105448739);
    interval const ssn(1.1056944561374e-17, 1.105694456137401e-17);
    interval const  cs(0.6933364607507921, 0.6933364607507955);
    interval const ccs(1.282283167453e-17, 1.282283167453002e-17);
    cerr << "x = " << x << endl;
    cerr << "sn = " << sn << endl;
    cerr << "ssn = " << ssn << endl;
    cerr << "cs = " << cs << endl;
    cerr << "ccs = " << ccs << endl;
    double big = 52776558133248;
    double sn3 = -1.66666666666664880952546298448555E-01;
    double sn5 =  8.33333214285722277379541354343671E-03;
    double cs2 =  4.99999999999999999999950396842453E-01;
    double cs4 = -4.16666666666664434524222570944589E-02;
    double cs6 =  1.38888874007937613028114285595617E-03;

    interval u = big + x;
    cerr << "u = big + x = " << u << endl;
    interval y = x - (u - big);
    cerr << "u - big = " << (u - big) << endl;
    cerr << "y = x - (u - big) = " << y << endl;
    interval xx = y * y;
    xx = sqr(y);
    interval s = y + y * xx * (sn3 + xx * sn5);
//    interval s = y + y * xx * sn3 + y * sqr(xx) * sn5;
    cerr << "s = " << s << endl;
//    interval c =  xx * cs2 + xx * xx * (cs4 + xx * cs6);
    interval c = xx * (cs2 + xx * (cs4 + xx * cs6));
    cerr << "c = " << c << endl;

    // interval const   s(-0.00781244302479111, -0.00740227132996466);
    // interval const   c(-8.203237153612913e-05, 8.613399011294674e-05);
    // interval const cor(-0.00547872095668542, -0.005073150929187586);
    // interval const res(0.7151352895881843, 0.7155408596156863);
    interval const cor = ssn + ((s* ccs) - (sn * c) + (cs * s));
    cerr << "cor = " << cor << endl;
    interval const res = sn + cor;
    cerr << "res = " << res << endl;

    //       x0 : [0.8046875, 0.8050976683527476];
    //     cor1 : [-0.0004055700275019417, -1.214306433183764e-17];
    //      cs0 : [0.6933364607507921, 0.6933364607507955];
    // tmp___10 : [103, 103];
    //       k0 : [412, 412];
    //     cs60 : [0.001388888740079375, 0.001388888740079381];
    //     cs40 : [-0.041667, -0.04166699999999999];
    //     cs20 : [0.5, 0.5];
    //      xx0 : [4.889056867782846e-05, 6.103515625e-05];
    //       y1 : [-0.0078125, -0.007402331647252512];
    //     sn50 : [0.00833333214285721, 0.008333332142857258];
    //     sn30 : [-0.166667, -0.1666669999999999];
    // tmp___00 : [52776558133248.81, 52776558133248.82];
    //       u0 : [52776558133248.81, 52776558133248.82];
    //     big0 : [52776558133248, 52776558133248];
    //     tmp0 : [3, 3];
    //       y0 : [3, 3];
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    interval::init();
    return RUN_ALL_TESTS();
}
