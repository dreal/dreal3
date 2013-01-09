/*
 * commonTests.hpp
 *
 *  Created on: 2009-09-02
 *      Author: iikapela
 */
#ifndef _UNITTESTS_INTERVALS_COMMONTESTS_HPP_
#define _UNITTESTS_INTERVALS_COMMONTESTS_HPP_

#include "../gtestHeader.h"

class FIXTURE_NAME: public ::testing::Test {
  protected:
  DInterval s1,s2,s3,s4; //intervals with small bounds
  DInterval b1,b2,b3,b4; //intervals with big  bounds
  DInterval m1,m2,m3,m4; //intervals with both small and big bounds


  FIXTURE_NAME() {
  s1 = DInterval(10E-100, 10E-99);
  s2 = DInterval(0.1, 0.3);
  s3 = DInterval(-0.0001, 0.00007);
  s4 = DInterval(-10E-111, -10E-112);

  b1 = DInterval(10E100, 10E101);
  b2 = DInterval(1000,10000);
  b3 = DInterval(-10E50, 10E50);
  b4 = DInterval(-10E49, -10E50);

  m1 = DInterval(-10E100, -10E-100);
  m2 = DInterval(10E-100, 10E100);
  m3 = DInterval(-10E-100, 10E100);
  m4 = DInterval(-10E100, 10E-100);
  }

  virtual ~FIXTURE_NAME() {
  }
  virtual void SetUp() {
  }
  virtual void TearDown() {
  }
};



TEST_F(FIXTURE_NAME, copyingConstructor) {
  DInterval cs1(s1),cs3(s3), cb2(b2), cb4(b4), cm1(m1), cm4(m4);
  EXPECT_EQ(s1,cs1) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(cs1,s1) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(s3,cs3) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(cs3,s3) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(b2,cb2) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(cb2,b2) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(b4,cb4) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(cb4,b4) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(m1,cm1) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(cm1,m1) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(m4,cm4) << "Copies made by copying constructor are different.\n";
  EXPECT_EQ(cm4,m4) << "Copies made by copying constructor are different.\n";
}

TEST_F(FIXTURE_NAME, oneArgumentConstructor) {
  DInterval a(3), b(10E-100), c(10E100), d(3.14), e(5.89345);
  EXPECT_EQ(3,a.leftBound()) << " One argument constructor doesn't work properly.\n";
  EXPECT_EQ(3,a.rightBound()) << " One argument constructor doesn't work properly.\n";

  EXPECT_EQ(10E-100,b.leftBound()) << " One argument constructor doesn't work properly.\n";
  EXPECT_EQ(10E-100,b.rightBound()) << " One argument constructor doesn't work properly.\n";

  EXPECT_EQ(10E100,c.leftBound()) << " One argument constructor doesn't work properly.\n";
  EXPECT_EQ(10E100,c.rightBound()) << " One argument constructor doesn't work properly.\n";

  EXPECT_EQ(3.14,d.leftBound()) << " One argument constructor doesn't work properly.\n";
  EXPECT_EQ(3.14,d.rightBound()) << " One argument constructor doesn't work properly.\n";

  EXPECT_EQ(5.89345,e.leftBound()) << " One argument constructor doesn't work properly.\n";
  EXPECT_EQ(5.89345,e.rightBound()) << " One argument constructor doesn't work properly.\n";
}

TEST_F(FIXTURE_NAME, twoArgumentConstructor) {
  EXPECT_EQ(10e-100, s1.leftBound()) << " Two argument constructor doesn't work properly.\n";
  EXPECT_EQ(10e-99, s1.rightBound()) << " Two argument constructor doesn't work properly.\n";
  EXPECT_EQ(10e100, b1.leftBound()) << " Two argument constructor doesn't work properly.\n";
  EXPECT_EQ(10e101, b1.rightBound()) << " Two argument constructor doesn't work properly.\n";
  EXPECT_EQ(-10E100, m1.leftBound()) << " Two argument constructor doesn't work properly.\n";
  EXPECT_EQ(-10E-100, m1.rightBound()) << " Two argument constructor doesn't work properly.\n";
}

/* There are no tests for leftBound() and rightBound() functions because
 * they were tested in oneArgumentConstructor and twoArgumentConstructor tests.
 */

TEST_F(FIXTURE_NAME, setBoundFunctions) {
  s1.setLeftBound(2342.234);
  EXPECT_EQ(2342.234, s1.leftBound()) << "setLeftBound() doesn't work properly.\n";
  EXPECT_EQ(10E-99, s1.rightBound()) << "setLeftBound() changed right bound.\n";

  b2.setLeftBound(-0.0001);
  EXPECT_EQ(-0.0001, b2.leftBound()) << "setLeftBound() doesn't work properly.\n";
  EXPECT_EQ(10000, b2.rightBound()) << "setLeftBound() changed right bound.\n";

  m4.setLeftBound(10E100);
  EXPECT_EQ(10E100, m4.leftBound()) << "setLeftBound() doesn't work properly.\n";
  EXPECT_EQ(10E-100, m4.rightBound()) << "setLeftBound() changed right bound.\n";

  s3.setRightBound(123.4545);
  EXPECT_EQ(123.4545, s3.rightBound()) << "setRightBound() doesn't work properly.\n";
  EXPECT_EQ(-0.0001, s3.leftBound()) << "setRightBound() changed left bound.\n";

  b1.setRightBound(3.1415927);
  EXPECT_EQ(3.1415927, b1.rightBound()) << "setRightBound() doesn't work properly.\n";
  EXPECT_EQ(10E100, b1.leftBound()) << "setRightBound() changed left bound.\n";

  m2.setRightBound(0);
  EXPECT_EQ(0, m2.rightBound()) << "setRightBound() doesn't work properly.\n";
  EXPECT_EQ(10E-100, m2.leftBound()) << "setRightBound() changed left bound.\n";
}

TEST_F(FIXTURE_NAME, leftAndRightFunctions) {
  EXPECT_EQ(DInterval(10E100), b1.left()) << "left() function doesn't work properly.\n";
  EXPECT_EQ(DInterval(1000), b2.left()) << "left() function doesn't work properly.\n";
  EXPECT_EQ(DInterval(-10E100), m1.left()) << "left() function doesn't work properly.\n";
  EXPECT_EQ(DInterval(10E-100), s1.left()) << "left() function doesn't work properly.\n";
  EXPECT_EQ(DInterval(10E-99), s1.right()) << "right() function doesn't work properly.\n";
  EXPECT_EQ(DInterval(-10E50), b4.right()) << "right() function doesn't work properly.\n";
  EXPECT_EQ(DInterval(10E-100), m4.right()) << "right() function doesn't work properly.\n";
  EXPECT_EQ(DInterval(10E100), m2.right()) << "right() function doesn't work properly.\n";
}

TEST_F(FIXTURE_NAME, containFunctionsForScalars) {
  DInterval a0(0), a1(1), am(10E-100), ad(10E100);
  EXPECT_TRUE(a0.contains(0)) << "a0 = " << a0 << "\n";
  EXPECT_TRUE(a1.contains(1)) << "a1 = " << a1 << "\n";
  EXPECT_TRUE(am.contains(10E-100))  << "am = " << am << "\n";
  EXPECT_TRUE(ad.contains(10E100))  << "ad = " << ad << "\n";

  EXPECT_FALSE(a0.contains(-10E-100)) << "a0 = " << a0 << "\n";
  EXPECT_FALSE(a0.contains(10E-100)) << "a0 = " << a0 << "\n";
  EXPECT_FALSE(a0.contains(-10E100)) << "a0 = " << a0 << "\n";
  EXPECT_FALSE(a0.contains(10E100)) << "a0 = " << a0 << "\n";

  EXPECT_FALSE(a1.contains(1.000001))  << "a1 = " << a1 << "\n";
  EXPECT_FALSE(a1.contains(0.99999)) << "a1 = " << a1 << "\n";
  EXPECT_FALSE(a1.contains(-1)) << "a1 = " << a1 << "\n";

  EXPECT_FALSE(am.contains(10E-99))  << "am = " << am << "\n";
  EXPECT_FALSE(am.contains(10E-101))  << "am = " << am << "\n";
  EXPECT_FALSE(am.contains(10E-101 + 10E-100))  << "am = " << am << "\n";
  EXPECT_FALSE(am.contains(10E-99 + 10E-100))  << "am = " << am << "\n";
  EXPECT_FALSE(am.contains(-10E-100))  << "am = " << am << "\n";
  EXPECT_FALSE(am.contains(0))  << "am = " << am << "\n";

  EXPECT_FALSE(ad.contains(10E101))  << "ad = " << ad << "\n";
  EXPECT_FALSE(ad.contains(10E99))  << "ad = " << ad << "\n";
  EXPECT_FALSE(ad.contains(10E101+10E100))  << "ad = " << ad << "\n";
  EXPECT_FALSE(ad.contains(10E99 +10E100))  << "ad = " << ad << "\n";
  EXPECT_FALSE(ad.contains(-10E100))  << "ad = " << ad << "\n";
  //tests for class variable s1
  //s1 = DInterval(10E-100, 10E-99);
  for(double scalar = 0; scalar < 10E-100; scalar += 10E-102) {
    ASSERT_FALSE(s1.contains(scalar)) << "s1 = " << s1 << "\nscalar = "  << std::scientific << scalar << std::fixed << "\n";
    //ASSERT to don't let thousand of errors apper on the screen at one time
  }

  for(double scalar = 10E-100; scalar <= 10E-99; scalar += 10E-102) {
    ASSERT_TRUE(s1.contains(scalar)) << "s1 = " << s1 << "\nscalar = " << std::scientific << scalar << std::fixed << "\n";
  }

  for(double scalar = 10E-99 + 10E-102; scalar <= 2*10e-99; scalar += 10E-102) {
    ASSERT_FALSE(s1.contains(scalar)) << "s1 = " << s1 << "\nscalar = " << std::scientific << scalar << std::fixed << "\n";
  }
}

TEST_F(FIXTURE_NAME, containsFunctionsForIntervals) {
  //tests for singletons:
  DInterval a0(0), a1(1), am(10E-100), ad(10E100);
  EXPECT_TRUE(a0.contains(a0)) << "Interval doesn't contain itself.\n";
  EXPECT_TRUE(a1.contains(a1)) << "Interval doesn't contain itself.\n";
  EXPECT_TRUE(am.contains(am)) << "Interval doesn't contain itself.\n";
  EXPECT_TRUE(ad.contains(ad)) << "Interval doesn't contain itself.\n";

  EXPECT_FALSE(a0.contains(a1)) << "a0 = " << a0 << "\na1 = " << a1;
  EXPECT_FALSE(a1.contains(a0)) << "a1 = " << a1 << "\na0 = " << a0;
  EXPECT_FALSE(a0.contains(am)) << "a0 = " << a0 << "\nam = " << am;
  EXPECT_FALSE(ad.contains(a0)) << "ad = " << ad << "\na0 = " << a0;
  EXPECT_FALSE(am.contains(a1)) << "am = " << am << "\na1 = " << a1;

  //test for intervals that aren't singletons
  EXPECT_FALSE(DInterval(30,40).contains(DInterval(20,40)));
  EXPECT_FALSE(DInterval(0,10E-100).contains(DInterval(0,10E-99)));
  EXPECT_FALSE(DInterval(-10E100,0).contains(DInterval(-10E101,0)));

  EXPECT_TRUE(DInterval(20,40).contains(DInterval(30,40)));
  EXPECT_TRUE(DInterval(0,10E-99).contains(DInterval(0,10E-100)));
  EXPECT_TRUE(DInterval(-10E101,0).contains(DInterval(-10E100,0)));
}

TEST_F(FIXTURE_NAME, containsInInteriorForScalars) {
  EXPECT_FALSE(s1.containsInInterior(s1)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(s2.containsInInterior(s2)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(s3.containsInInterior(s3)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(s4.containsInInterior(s4)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(b1.containsInInterior(b1)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(b2.containsInInterior(b2)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(b3.containsInInterior(b3)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(b4.containsInInterior(b4)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(m1.containsInInterior(m1)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(m2.containsInInterior(m2)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(m3.containsInInterior(m3)) << "Interval contains itself in its interior\n";
  EXPECT_FALSE(m4.containsInInterior(m4)) << "Interval contains itself in its interior\n";

  //s1 = DInterval(10E-100, 10E-99);
  EXPECT_TRUE(s1.containsInInterior(10E-99 - 10E-100)) << "s1 = " << s1;
  EXPECT_TRUE(s1.containsInInterior(10E-100 + 10E-101 )) << "s1 = " << s1;
  EXPECT_FALSE(s1.containsInInterior(10E-99 + 10E-100)) << "s1 = " << s1;
  EXPECT_FALSE(s1.containsInInterior(10E-100 - 10E-101)) << "s1 = " << s1;
  EXPECT_FALSE(s1.containsInInterior(10E-100)) << "s1 = " << s1;
  EXPECT_FALSE(s1.containsInInterior(10E-99)) << "s1 = " << s1;

  //b3 = DInterval(-10E50, 10E50);
  EXPECT_TRUE(b3.containsInInterior(50000)) << "b3 = " << b3;
  EXPECT_TRUE(b3.containsInInterior(-1)) << "b3 = " << b3;
  EXPECT_TRUE(b3.containsInInterior(-10E50 + 10E49)) << "b3 = " << b3;
  EXPECT_TRUE(b3.containsInInterior(10E50 - 10E49)) << "b3 = " << b3;
  EXPECT_FALSE(b3.containsInInterior(-10E50 - 10E49)) << "b3 = " << b3;
  EXPECT_FALSE(b3.containsInInterior(10E50 + 10E49)) << "b3 = " << b3;
  EXPECT_FALSE(b3.containsInInterior(-10E50)) << "b3 = " << b3;
  EXPECT_FALSE(b3.containsInInterior(10E50)) << "b3 = " << b3;

  //m2 = DInterval(10E-100, 10E100);
  EXPECT_TRUE(m2.containsInInterior(10E99))  << "m2 = " << m2;
  EXPECT_TRUE(m2.containsInInterior(10E-99))  << "m2 = " << m2;
  EXPECT_TRUE(m2.containsInInterior(10E100-10E99))  << "m2 = " << m2;
  EXPECT_TRUE(m2.containsInInterior(10E-100+10E-101))  << "m2 = " << m2;
  EXPECT_FALSE(m2.containsInInterior(-1))  << "m2 = " << m2;
  EXPECT_FALSE(m2.containsInInterior(0))  << "m2 = " << m2;
  EXPECT_FALSE(m2.containsInInterior(10E-101))  << "m2 = " << m2;
  EXPECT_FALSE(m2.containsInInterior(-10E-100))  << "m2 = " << m2;
  EXPECT_FALSE(m2.containsInInterior(10E-100))  << "m2 = " << m2;
  EXPECT_FALSE(m2.containsInInterior(10E100))  << "m2 = " << m2;
  EXPECT_FALSE(m2.containsInInterior(10E100+10E99))  << "m2 = " << m2;
  EXPECT_FALSE(m2.containsInInterior(10E-100-10E-101))  << "m2 = " << m2;
}

TEST_F(FIXTURE_NAME, containsInInteriorForIntervals) {
  EXPECT_FALSE(s1.containsInInterior(s1)) << "Interval contain itself in interior.";
  EXPECT_FALSE(s3.containsInInterior(s3)) << "Interval contain itself in interior.";
  EXPECT_FALSE(b1.containsInInterior(b1)) << "Interval contain itself in interior.";
  EXPECT_FALSE(b2.containsInInterior(b2)) << "Interval contain itself in interior.";
  EXPECT_FALSE(m3.containsInInterior(m3)) << "Interval contain itself in interior.";
  EXPECT_FALSE(m4.containsInInterior(m4)) << "Interval contain itself in interior.";

  EXPECT_FALSE(s2.containsInInterior( DInterval(s2)) ) << "Interval contains the same interval in it's interior";
  EXPECT_FALSE(b3.containsInInterior( DInterval(b3)) ) << "Interval contains the same interval in it's interior";
  EXPECT_FALSE(m1.containsInInterior( DInterval(m1)) ) << "Interval contains the same interval in it's interior";

  //    s4 = DInterval(-10E-111, -10E-112);        [      s4      ]
  DInterval s4_1(-10E-111 -10E-112, -10E-112);      //     [       s4_1     ]
  DInterval s4_2(-10E-111 + 10E-112, -10E-112-10E-113);   //        [    s4_2   ]
  DInterval s4_3(-10E-111 - 10E-112, -10E-112+10E-113);   //     [       s4_3       ]
  DInterval s4_4(-10E-111, -10E-112+10E-113);             //       [     s4_4       ]

  DInterval s4_0(s4);

  EXPECT_FALSE(s4_0.containsInInterior(s4_1)) << "s4_0 = " << s4_0 << "s4_1 = " << s4_1 << "\n";
  EXPECT_TRUE (s4_0.containsInInterior(s4_2)) << "s4_0 = " << s4_0 << "s4_2 = " << s4_2 << "\n";
  EXPECT_FALSE(s4_0.containsInInterior(s4_3)) << "s4_0 = " << s4_0 << "s4_3 = " << s4_3 << "\n";
  EXPECT_FALSE(s4_0.containsInInterior(s4_4)) << "s4_0 = " << s4_0 << "s4_4 = " << s4_4 << "\n";

  EXPECT_FALSE(s4_1.containsInInterior(s4_0)) << "s4_1 = " << s4_1 << "s4_0 = " << s4_0 << "\n";
  EXPECT_TRUE (s4_1.containsInInterior(s4_2)) << "s4_1 = " << s4_1 << "s4_2 = " << s4_2 << "\n";
  EXPECT_FALSE(s4_1.containsInInterior(s4_3)) << "s4_1 = " << s4_1 << "s4_3 = " << s4_3 << "\n";
  EXPECT_FALSE(s4_1.containsInInterior(s4_4)) << "s4_1 = " << s4_1 << "s4_4 = " << s4_4 << "\n";

  EXPECT_FALSE(s4_2.containsInInterior(s4_0)) << "s4_2 = " << s4_2 << "s4_0 = " << s4_0 << "\n";
  EXPECT_FALSE(s4_2.containsInInterior(s4_1)) << "s4_2 = " << s4_2 << "s4_1 = " << s4_1 << "\n";
  EXPECT_FALSE(s4_2.containsInInterior(s4_3)) << "s4_2 = " << s4_2 << "s4_3 = " << s4_3 << "\n";
  EXPECT_FALSE(s4_2.containsInInterior(s4_4)) << "s4_2 = " << s4_2 << "s4_4 = " << s4_4 << "\n";

  EXPECT_TRUE (s4_3.containsInInterior(s4_0)) << "s4_3 = " << s4_3 << "s4_0 = " << s4_0 << "\n";
  EXPECT_FALSE(s4_3.containsInInterior(s4_1)) << "s4_3 = " << s4_3 << "s4_1 = " << s4_1 << "\n";
  EXPECT_TRUE (s4_3.containsInInterior(s4_2)) << "s4_3 = " << s4_3 << "s4_2 = " << s4_2 << "\n";
  EXPECT_FALSE(s4_3.containsInInterior(s4_4)) << "s4_3 = " << s4_3 << "s4_4 = " << s4_4 << "\n";

  EXPECT_FALSE(s4_4.containsInInterior(s4_0)) << "s4_4 = " << s4_4 << "s4_0 = " << s4_0 << "\n";
  EXPECT_FALSE(s4_4.containsInInterior(s4_1)) << "s4_4 = " << s4_4 << "s4_1 = " << s4_1 << "\n";
  EXPECT_TRUE(s4_4.containsInInterior(s4_2)) << "s4_4 = " << s4_4 << "s4_2 = " << s4_2 << "\n";
  EXPECT_FALSE(s4_4.containsInInterior(s4_3)) << "s4_4 = " << s4_4 << "s4_3 = " << s4_3 << "\n";
}

TEST_F(FIXTURE_NAME, logicalOperators) {
  DInterval a1(10e-100, 5.2323);
  DInterval a2(10e-100, 5.2323);
  DInterval a3(10e-100, 5.2524);
  DInterval a4(10e-99,  5.2323);
  EXPECT_EQ(a1,a2);
  EXPECT_EQ(a2,a1);

  EXPECT_NE(a1,a3);
  EXPECT_NE(a3,a1);
  EXPECT_NE(a2,a3);
  EXPECT_NE(a3,a2);

  EXPECT_NE(a1,a4);
  EXPECT_NE(a4,a1);
  EXPECT_NE(a2,a4);
  EXPECT_NE(a4,a2);
  EXPECT_NE(a3,a4);
  EXPECT_NE(a4,a3);

  EXPECT_EQ(a1,a1);
  EXPECT_EQ(a2,a2);
  EXPECT_EQ(a3,a3);
  EXPECT_EQ(a4,a4);

  DInterval b1(-10e100, 10e-34);
  DInterval b2(-10e100, 10e-34);
  DInterval b3(-10e100, 10e-34+10e-33);
  DInterval b4(-10e100 -10e101, 10e-34);

  EXPECT_EQ(b1,b2);
  EXPECT_EQ(b2,b1);

  EXPECT_NE(b1,b3);
  EXPECT_NE(b3,b1);
  EXPECT_NE(b2,b3);
  EXPECT_NE(b3,b2);

  EXPECT_NE(b1,b4);
  EXPECT_NE(b4,b1);
  EXPECT_NE(b2,b4);
  EXPECT_NE(b4,b2);
  EXPECT_NE(b3,b4);
  EXPECT_NE(b4,b2);

  EXPECT_EQ(b1,b1);
  EXPECT_EQ(b2,b2);
  EXPECT_EQ(b3,b3);
  EXPECT_EQ(b4,b4);

  DInterval c1(3.14,3.14);
  DInterval c2(3.14,3.14);
  DInterval c3(3.14,3.15);
  DInterval c4(3.13,3.14);

  EXPECT_EQ(c1,c2);
  EXPECT_EQ(c2,c1);

  EXPECT_NE(c1,c3);
  EXPECT_NE(c3,c1);
  EXPECT_NE(c2,c3);
  EXPECT_NE(c3,c2);

  EXPECT_NE(c1,c4);
  EXPECT_NE(c4,c1);
  EXPECT_NE(c2,c4);
  EXPECT_NE(c4,c2);
  EXPECT_NE(c3,c4);
  EXPECT_NE(c4,c2);

  EXPECT_EQ(c1,c1);
  EXPECT_EQ(c2,c2);
  EXPECT_EQ(c3,c3);
  EXPECT_EQ(c4,c4);

  DInterval singleton(-164.2363);
  EXPECT_TRUE(singleton <= singleton);
  EXPECT_FALSE(singleton < singleton);
  EXPECT_TRUE(singleton >= singleton);
  EXPECT_FALSE(singleton > singleton);

  DInterval d(-3.15,-1.17),
            e(-1.17, 0.0001),
            f(-3.14, -2.83),
            g(0.0001, 12),
            h(-2, 10);
  EXPECT_FALSE(d < d);
  EXPECT_FALSE(e < e);
  EXPECT_FALSE(f < f);
  EXPECT_FALSE(g < g);
  EXPECT_FALSE(h < h);

  EXPECT_FALSE(d > d);
  EXPECT_FALSE(e > e);
  EXPECT_FALSE(f > f);
  EXPECT_FALSE(g > g);
  EXPECT_FALSE(h > h);

  EXPECT_TRUE(d < g);
  EXPECT_TRUE(d <= g);
  EXPECT_FALSE(d > g);
  EXPECT_FALSE(d >= g);

  EXPECT_TRUE(d <= e);
  EXPECT_FALSE(d < e);
  EXPECT_FALSE(d >= e);
  EXPECT_FALSE(d > e);

  EXPECT_FALSE(d < h);
  EXPECT_FALSE(d <= h);
  EXPECT_FALSE(d > h);
  EXPECT_FALSE(d >= h);

  EXPECT_FALSE(d < f);
  EXPECT_FALSE(d <= f);
  EXPECT_FALSE(d > f);
  EXPECT_FALSE(d >= f);

  EXPECT_TRUE(f <= e);
  EXPECT_TRUE(f < e);
  EXPECT_FALSE(f >= e);
  EXPECT_FALSE(f > e);

  EXPECT_TRUE(f <= g);
  EXPECT_TRUE(f < g);
  EXPECT_FALSE(f >= g);
  EXPECT_FALSE(f > g);

  EXPECT_TRUE(f <= h);
  EXPECT_TRUE(f < h);
  EXPECT_FALSE(f >= h);
  EXPECT_FALSE(f > h);

  EXPECT_TRUE(e <= g);
  EXPECT_FALSE(e < g);
  EXPECT_FALSE(e >= g);
  EXPECT_FALSE(e > g);

  EXPECT_FALSE(e < h);
  EXPECT_FALSE(e <= h);
  EXPECT_FALSE(e > h);
  EXPECT_FALSE(e >= h);

  EXPECT_FALSE(g < h);
  EXPECT_FALSE(g <= h);
  EXPECT_FALSE(g > h);
  EXPECT_FALSE(g >= h);
}

TEST_F(FIXTURE_NAME, midFunction) {
  srand(12345); //if I enforce seed, random values are deterministic, so tests are still repetable
  for(int i=0; i < 1000000; ++i) { //I use ASSERT in this loop instead of EXPECT to not let million of error messages appear on the screen at once
    double scalar = 1.0 / static_cast<double>(rand());
    if(rand()%2) scalar *= 10E100;
    DInterval a(-scalar,scalar);
    ASSERT_EQ(0.0, a.mid()) << "Schould be equal to 0, because bounds are equal with opposite sign.\na = " << a << "\n";
    if(rand() % 2) scalar  *= -1;
    DInterval b(scalar);
    ASSERT_EQ(scalar, b.mid()) << "Schould be equal to scalar, because b is a singleton [scalar, scalar].\nscalar = " << scalar << ", b = " << b << "\n";
    }
}

TEST_F(FIXTURE_NAME, splitTwoArgumentFunction) {
  DInterval mid, remainder;

  DInterval a(-10E100, 10E100);
  a.split(mid,remainder);
  EXPECT_EQ(a,remainder);
  EXPECT_EQ(0,mid);

  DInterval b(5);
  b.split(mid,remainder);
  EXPECT_EQ(0,remainder);
  EXPECT_EQ(5,mid);

  DInterval c(10E-101, 10E-100);
  c.split(mid,remainder);
  EXPECT_EQ(DInterval(-4.5*10E-101, 4.5*10E-101), remainder);
  EXPECT_EQ(5.5*10E-101, mid);
}

TEST_F(FIXTURE_NAME, splitOneArgumentFunction) {
  DInterval tmp, remainder;

  DInterval a(-10E100, 10E100);
  tmp = a;
  a.split(remainder);
  EXPECT_EQ(tmp,remainder);
  EXPECT_EQ(0,a);

  DInterval b(5);
  b.split(remainder);
  EXPECT_EQ(0,remainder);
  EXPECT_EQ(5,b);

  DInterval c(10E-101, 10E-100);
  c.split(remainder);
  EXPECT_EQ( DInterval(-4.5*10E-101,4.5*10E-101), remainder);
  EXPECT_EQ(5.5*10E-101, c);
}

TEST_F(FIXTURE_NAME, assignmentOperator) {
  DInterval cs1,cs3, cb2, cb4, cm1, cm4;
  cs1 = s1;
  cs3 = s3;
  cb2 = b2;
  cb4 = b4;
  cm1 = m1;
  cm4 = m4;
  EXPECT_EQ(s1,cs1) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(cs1,s1) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(s3,cs3) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(cs3,s3) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(b2,cb2) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(cb2,b2) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(b4,cb4) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(cb4,b4) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(m1,cm1) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(cm1,m1) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(m4,cm4) << "Copies made by assignment operator are different.\n";
  EXPECT_EQ(cm4,m4) << "Copies made by assignment operator are different.\n";

  DInterval a;
  srand(12345); //if I enforce seed, random values are deterministic, so tests are still repetable
  for(int i=0; i < 1000000; ++i) { //I use ASSERT in this loop instead of EXPECT to not let million of error messages appear on the screen at once
    double scalar = 1.0 / static_cast<double>(rand());
    if(rand()%2) scalar *= 10E100;
    if(rand() % 2) scalar  *= -1;
    a = scalar;
    ASSERT_EQ(scalar, a.leftBound());
    ASSERT_EQ(scalar, a.rightBound());
  }
}

TEST_F(FIXTURE_NAME, AdditionOperator) {
  DInterval result;
  result = s1 + s2;
  EXPECT_EQ(0.1, result.leftBound());
  EXPECT_LT(0.3, result.rightBound());

  result = s2 + s1;
  EXPECT_EQ(0.1, result.leftBound());
  EXPECT_LT(0.3, result.rightBound());

  result = s3 + s4;
  EXPECT_EQ(0.00007, result.rightBound());
  EXPECT_GT(-0.0001, result.leftBound());

  result = s4 + s3;
  EXPECT_EQ(0.00007, result.rightBound());
  EXPECT_GT(-0.0001, result.leftBound());

  result = b1 + b2;
  EXPECT_EQ(10E100, result.leftBound());
  EXPECT_LT(10E101, result.rightBound());

  result = b2 + b1;
  EXPECT_EQ(10E100, result.leftBound());
  EXPECT_LT(10E101, result.rightBound());

  result = m3 + s4;
  EXPECT_GE(-10e-100 - 10e-111, result.leftBound());
  EXPECT_EQ(10e100, result.rightBound());

  result = s4 + m3;
  EXPECT_GE(-10e-100 - 10e-111, result.leftBound());
  EXPECT_EQ(10e100, result.rightBound());

  DInterval  a(0.3, 1), b(-0.1);
  result = a + b;
  EXPECT_GE(0.2, result.leftBound());
  EXPECT_LE(0.9, result.rightBound());

  result = a + b;
  result = result + b;
  result = result + b;
  EXPECT_GE(0, result.leftBound());
  EXPECT_LE(0.7, result.rightBound());

  DInterval small(-0.001);
  result = DInterval(10,10);
  for (int i = 0; i<10000; ++i) result = result + small;
  EXPECT_GE(0, result.leftBound());
  EXPECT_LE(0, result.rightBound());
}

TEST_F(FIXTURE_NAME, AdditionAndAssignmentOperator) {
  DInterval result;
  result = s1;
  result += s2;
  EXPECT_EQ(0.1, result.leftBound());
  EXPECT_LT(0.3, result.rightBound());

  result = s2;
  result += s1;
  EXPECT_EQ(0.1, result.leftBound());
  EXPECT_LT(0.3, result.rightBound());

  result = s3;
  result += s4;
  EXPECT_EQ(0.00007, result.rightBound());
  EXPECT_GT(-0.0001, result.leftBound());

  result = s4;
  result += s3;
  EXPECT_EQ(0.00007, result.rightBound());
  EXPECT_GT(-0.0001, result.leftBound());

  result = b1;
  result += b2;
  EXPECT_EQ(10E100, result.leftBound());
  EXPECT_LT(10E101, result.rightBound());

  result = b2;
  result += b1;
  EXPECT_EQ(10E100, result.leftBound());
  EXPECT_LT(10E101, result.rightBound());

  result = m3;
  result += s4;
  EXPECT_GE(-10e-100 - 10e-111, result.leftBound());
  EXPECT_EQ(10e100, result.rightBound());

  result = s4;
  result += m3;
  EXPECT_GE(-10e-100 - 10e-111, result.leftBound());
  EXPECT_EQ(10e100, result.rightBound());


  DInterval  a(0.3, 1), b(-0.1);
  result = a;
  result += b;
  EXPECT_GE(0.2, result.leftBound());
  EXPECT_LE(0.9, result.rightBound());

  result = a;
  result += b;
  result += b;
  result += b;
  EXPECT_GE(0, result.leftBound());
  EXPECT_LE(0.7, result.rightBound());

  DInterval small(-0.001);
  result = DInterval(10,10);
  for (int i = 0; i<10000; ++i) result += small;
  EXPECT_GE(0, result.leftBound());
  EXPECT_LE(0, result.rightBound());
}

TEST_F(FIXTURE_NAME, UnarySubtractOperator) {
  DInterval z1(0), z2(0, 1), z3(-1,0);
  DInterval n1(1), n2(-1), n3(-1, 1), n4(1, 2), n5(-2, -1);

  EXPECT_EQ(z1, -z1);
  EXPECT_EQ(-z1, z1);
  EXPECT_EQ(z2, -z3);
  EXPECT_EQ(-z3, z2);
  EXPECT_EQ(z3, -z2);
  EXPECT_EQ(-z2, z3);
  EXPECT_EQ(n1,-n2);
  EXPECT_EQ(-n2,n1);
  EXPECT_EQ(n2,-n1);
  EXPECT_EQ(-n1,n2);
  EXPECT_EQ(n3,-n3);
  EXPECT_EQ(-n3,n3);
  EXPECT_EQ(n4,-n5);
  EXPECT_EQ(-n5,n4);
  EXPECT_EQ(n5,-n4);
  EXPECT_EQ(-n4,n5);
}

TEST_F(FIXTURE_NAME, SubtractionOperator) {
  DInterval result;
  result = s1 - s2;
  EXPECT_EQ(-0.3, result.leftBound());
  EXPECT_LT(-0.1, result.rightBound());

  result = s2 - s1;
  EXPECT_GT(0.1, result.leftBound());
  EXPECT_EQ(0.3, result.rightBound());

  result = s3 - s4;
  EXPECT_EQ(-0.0001, result.leftBound());
  EXPECT_LT(0.00007, result.rightBound());

  result = s4 - s3;
  EXPECT_GT(-0.00007, result.leftBound());
  EXPECT_EQ(0.0001, result.rightBound());

  result = b1 - b2;
  EXPECT_GT(10E100, result.leftBound());
  EXPECT_EQ(10E101, result.rightBound());

  result = b2 - b1;
  EXPECT_EQ(-10E101, result.leftBound());
  EXPECT_LT(-10E100, result.rightBound());

  result = m3 - s4;
  EXPECT_GE(-10e-100 + 10e-111, result.leftBound());
  EXPECT_LT(10e100, result.rightBound());

  result = s4 - m3;
  EXPECT_GE(-10e100, result.leftBound());
  EXPECT_LE(-10e-112 + 10e-100, result.rightBound());

  DInterval  a(0.3, 1), b(0.1);
  result = a - b;
  EXPECT_GE(0.2, result.leftBound());
  EXPECT_LE(0.9, result.rightBound());

  result = a - b;
  result = result - b;
  result = result - b;
  EXPECT_GE(0, result.leftBound());
  EXPECT_LE(0.7, result.rightBound());

  DInterval small(0.001);
  result = DInterval(10,10);
  for (int i = 0; i<10000; ++i) result = result - small;
  EXPECT_GE(0, result.leftBound());
  EXPECT_LE(0, result.rightBound());
}

TEST_F(FIXTURE_NAME, SubtractionAndAssignmentOperator) {
  DInterval result;
  result = s1;
  result -= s2;
  EXPECT_EQ(-0.3, result.leftBound());
  EXPECT_LT(-0.1, result.rightBound());

  result = s2;
  result -= s1;
  EXPECT_GT(0.1, result.leftBound());
  EXPECT_EQ(0.3, result.rightBound());

  result = s3;
  result -= s4;
  EXPECT_EQ(-0.0001, result.leftBound());
  EXPECT_LT(0.00007, result.rightBound());

  result = s4;
  result -= s3;
  EXPECT_GT(-0.00007, result.leftBound());
  EXPECT_EQ(0.0001, result.rightBound());

  result = b1;
  result -= b2;
  EXPECT_GT(10E100, result.leftBound());
  EXPECT_EQ(10E101, result.rightBound());

  result = b2;
  result -= b1;
  EXPECT_EQ(-10E101, result.leftBound());
  EXPECT_LT(-10E100, result.rightBound());

  result = m3;
  result -= s4;
  EXPECT_GE(-10e-100 + 10e-111, result.leftBound());
  EXPECT_LT(10e100, result.rightBound());

  result = s4;
  result -= m3;
  EXPECT_GE(-10e100, result.leftBound());
  EXPECT_LE(-10e-112 + 10e-100, result.rightBound());

  DInterval  a(0.3, 1), b(0.1);
  result = a;
  result -= b;
  EXPECT_GE(0.2, result.leftBound());
  EXPECT_LE(0.9, result.rightBound());

  result = DInterval(1,2);
  result -= result;
  EXPECT_GE(-1, result.leftBound());
  EXPECT_LE(1, result.rightBound());
  EXPECT_LE(-1.00001, result.leftBound());
  EXPECT_GE(1.00001, result.rightBound());


  result = a;
  result -= b;
  result -= b;
  result -= b;
  EXPECT_GE(0, result.leftBound());
  EXPECT_LE(0.7, result.rightBound());

  DInterval small(0.001);
  result = DInterval(10,10);
  for (int i = 0; i<10000; ++i) result -= small;
  EXPECT_GE(0, result.leftBound());
  EXPECT_LE(0, result.rightBound());
}

TEST_F(FIXTURE_NAME, multiplicationOpetator) {
  DInterval a(0.001, 0.01);
  a =a * a;
  EXPECT_GE(1e-6, a.leftBound());
  EXPECT_LE(1e-5, a.rightBound());

  DInterval b(-0.01, -0.001);
  b =b * b;
  EXPECT_GE(1e-6, b.leftBound());
  EXPECT_LE(1e-5, b.rightBound());

  DInterval c(-0.1, 0.1);
  c =c * c;
  EXPECT_GE(-0.01, c.leftBound());
  EXPECT_LE(0.01, c.rightBound());

  DInterval d(-1.1, 1.1);
  d =d * d;
  EXPECT_GE(-1.21, d.leftBound());
  EXPECT_LE(1.21, d.rightBound());

  DInterval e(0,2),f(-1, 3);
  EXPECT_GE(-2, (e*f).leftBound());
  EXPECT_LE(6, (e*f).rightBound());
  EXPECT_GE(-2, (f*e).leftBound());
  EXPECT_LE(6, (f*e).rightBound());

  DInterval g(-15, -11), h(0.1,12);
  EXPECT_GE(-180, (g*h).leftBound());
  EXPECT_LE(-1.1, (g*h).rightBound());
  EXPECT_GE(-180, (h*g).leftBound());
  EXPECT_LE(-1.1, (h*g).rightBound());

  DInterval i(-1000, 10), j(10, 15);
  EXPECT_GE(-15000, (i*j).leftBound());
  EXPECT_LE(150, (i*j).rightBound());
  EXPECT_GE(-15000, (j*i).leftBound());
  EXPECT_LE(150, (j*i).rightBound());

  DInterval k(-15, -5), l(-1, 5);
  EXPECT_GE(-75, (k*l).leftBound());
  EXPECT_LE(-15, (k*l).rightBound());
  EXPECT_GE(-75, (l*k).leftBound());
  EXPECT_LE(-15, (l*k).rightBound());

  DInterval m(1,5), n(3,8);
  EXPECT_GE(3, (m*n).leftBound());
  EXPECT_LE(40, (m*n).rightBound());
  EXPECT_GE(3, (n*m).leftBound());
  EXPECT_LE(40, (n*m).rightBound());

  DInterval o(-1,15), p(0,12);
  EXPECT_GE(-12, (o*p).leftBound());
  EXPECT_LE(180, (o*p).rightBound());
  EXPECT_GE(-12, (p*o).leftBound());
  EXPECT_LE(180, (p*o).rightBound());
}

TEST_F(FIXTURE_NAME, multiplicationAndAssignmentOpetator) {
  DInterval a(0.001, 0.01);
  a *= a;
  EXPECT_GE(1e-6, a.leftBound());
  EXPECT_LE(1e-5, a.rightBound());

  DInterval b(-0.01, -0.001);
  b *= b;
  EXPECT_GE(1e-6, b.leftBound());
  EXPECT_LE(1e-5, b.rightBound());

  DInterval c(-0.1, 0.1);
  c *= c;
  EXPECT_GE(-0.01, c.leftBound());
  EXPECT_LE(0.01, c.rightBound());

  DInterval d(-1.1, 1.1);
  d *= d;
  EXPECT_GE(-1.21, d.leftBound());
  EXPECT_LE(1.21, d.rightBound());

  DInterval result;

  DInterval e(0,2),f(-1, 3);
  result = e;
  result *= f;
  EXPECT_GE(-2, result.leftBound());
  EXPECT_LE(6, result.rightBound());
  result = f;
  result *= e;
  EXPECT_GE(-2, result.leftBound());
  EXPECT_LE(6, result.rightBound());

  DInterval g(-15, -11), h(0.1,12);
  result = g;
  result *= h;
  EXPECT_GE(-180, result.leftBound());
  EXPECT_LE(-1.1, result.rightBound());
  result = h;
  result *= g;
  EXPECT_GE(-180, result.leftBound());
  EXPECT_LE(-1.1, result.rightBound());

  DInterval i(-1000, 10), j(10, 15);
  result = i;
  result *= j;
  EXPECT_GE(-15000, result.leftBound());
  EXPECT_LE(150, result.rightBound());
  result = j;
  result *= i;
  EXPECT_GE(-15000, result.leftBound());
  EXPECT_LE(150, result.rightBound());

  DInterval k(-15, -5), l(-1, 5);
  result = k;
  result *= l;
  EXPECT_GE(-75, result.leftBound());
  EXPECT_LE(-15, result.rightBound());
  result = l;
  result *= k;
  EXPECT_GE(-75, result.leftBound());
  EXPECT_LE(-15, result.rightBound());


  DInterval m(1,5), n(3,8);
  result = m;
  result *= n;
  EXPECT_GE(3, result.leftBound());
  EXPECT_LE(40, result.rightBound());
  result = n;
  result *= m;
  EXPECT_GE(3, result.leftBound());
  EXPECT_LE(40, result.rightBound());

  DInterval o(-1,15), p(0,12);
  result = o;
  result *= p;
  EXPECT_GE(-12, result.leftBound());
  EXPECT_LE(180, result.rightBound());
  result = p;
  result *= o;
  EXPECT_GE(-12, result.leftBound());
  EXPECT_LE(180, result.rightBound());
}

TEST_F(FIXTURE_NAME, divisionOpetator) {
  DInterval a(0.001, 0.01);
  EXPECT_GE(0.1, (a/a).leftBound());
  EXPECT_LE(10, (a/a).rightBound());
  a = a / a;
  EXPECT_GE(0.1, a.leftBound());
  EXPECT_LE(10, a.rightBound());

  DInterval b(-0.01, -0.001);
  EXPECT_GE(0.1, (b/b).leftBound());
  EXPECT_LE(10, (b/b).rightBound());
  b = b / b;
  EXPECT_GE(0.1, b.leftBound());
  EXPECT_LE(10, b.rightBound());

  DInterval c(-0.1, 0.1), c1(1e-100, 0.1);
  EXPECT_THROW(b / c, capd::intervals::IntervalError<double>);
  c = c / c1;
  EXPECT_GE(-1e99, c.leftBound());
  EXPECT_LE(1e99, c.rightBound());

  DInterval d(-1.1, 1.1), d1(-1.1, -0.5);
  d =d / d1;
  EXPECT_GE(-2.2, d.leftBound());
  EXPECT_LE(2.2, d.rightBound());

  DInterval e(0.11,2),f(-1, 3), f1(0.12,3);
  EXPECT_GE(-1/0.11, (f/e).leftBound());
  EXPECT_LE(3/0.11, (f/e).rightBound());
  EXPECT_GE(0.11/3, (e/f1).leftBound());
  EXPECT_LE(2/0.12, (e/f1).rightBound());
  EXPECT_GE(0.06, (f1/e).leftBound());
  EXPECT_LE(3/0.11, (f1/e).rightBound());

  e = DInterval(-2, -0.17);
  f = DInterval(-3, 1);
  f1 = DInterval(-3,-0.12);
  EXPECT_GE(1/-0.17, (f/e).leftBound());
  EXPECT_LE(-3/-0.17, (f/e).rightBound());
  EXPECT_GE(0.17/3, (e/f1).leftBound());
  EXPECT_LE(2/0.12, (e/f1).rightBound());
  EXPECT_GE(0.12/2, (f1/e).leftBound());
  EXPECT_LE(3/0.17, (f1/e).rightBound());

  DInterval g(-15, -11), h(0.1,12);
  EXPECT_GE(-15/0.1, (g/h).leftBound());
  EXPECT_LE(-11.0/12.0, (g/h).rightBound());
  EXPECT_GE(-12.0/-11.0, (h/g).leftBound());
  EXPECT_LE(-0.1/15, (h/g).rightBound());

  DInterval i(-1000, 10), j(10, 15);
  EXPECT_GE(-100, (i/j).leftBound());
  EXPECT_LE(1, (i/j).rightBound());

  DInterval i1(-1000, -10), j1(-10, -5);
  EXPECT_GE(1, (i1/j1).leftBound());
  EXPECT_LE(200, (i1/j1).rightBound());
  EXPECT_GE(5e-3, (j1/i1).leftBound());
  EXPECT_LE(1, (j1/i1).rightBound());

  DInterval i2(-14.1, -0.3), j2(-0.3, 12.21);
  EXPECT_GE(-12.21/0.3, (j2/i2).leftBound());
  EXPECT_LE(1, (j2/i2).rightBound());

  DInterval i3(-11.1, -10.1), j3(-10.1, -10);
  EXPECT_GE(1, (i3/j3).leftBound());
  EXPECT_LE(1.11, (i3/j3).rightBound());
  EXPECT_GE(10/11.1, (j3/i3).leftBound());
  EXPECT_LE(1, (j3/i3).rightBound());

  DInterval i4(0.01, 0.1), j4(0.1, 1.1);
  EXPECT_GE(1.0/110, (i4/j4).leftBound());
  EXPECT_LE(1, (i4/j4).rightBound());
  EXPECT_GE(1, (j4/i4).leftBound());
  EXPECT_LE(110, (j4/i4).rightBound());

  DInterval i5(0.1, 3.15), j5(3.15, 32);
  EXPECT_GE(0.1/32, (i5/j5).leftBound());
  EXPECT_LE(1, (i5/j5).rightBound());
  EXPECT_GE(1, (j5/i5).leftBound());
  EXPECT_LE(320, (j5/i5).rightBound());

  DInterval k(-15, -5), l(-1, 5);
  EXPECT_GE(-1, (l/k).leftBound());
  EXPECT_LE(0.2, (l/k).rightBound());

  DInterval k1(-15, -5), l1(1, 5);
  EXPECT_GE(-15, (k1/l1).leftBound());
  EXPECT_LE(-1, (k1/l1).rightBound());
  EXPECT_GE(-1, (l1/k1).leftBound());
  EXPECT_LE(-1.0/15.0, (l1/k1).rightBound());

  DInterval m(1,5), n(3,8);
  EXPECT_GE(1.0/8.0, (m/n).leftBound());
  EXPECT_LE(5.0/3.0, (m/n).rightBound());
  EXPECT_GE(3.0/5.0, (n/m).leftBound());
  EXPECT_LE(8, (n/m).rightBound());

  DInterval o(-1,15), p(0.01,12);
  EXPECT_GE(-100, (o/p).leftBound());
  EXPECT_LE(1500, (o/p).rightBound());

  DInterval q(10000, 5000000), q1(q);
  EXPECT_GE(1.0/500, (q/q1).leftBound());
  EXPECT_LE(500, (q/q1).rightBound());
  EXPECT_GE(1.0/500, (q/q).leftBound());
  EXPECT_LE(500, (q/q).rightBound());
  q = q / q;
  EXPECT_GE(1.0/500, q.leftBound());
  EXPECT_LE(500, q.rightBound());

  DInterval r(-3.14, -3.12), s(r);
  EXPECT_GE(3.12/3.14, (r/s).leftBound());
  EXPECT_LE(3.14/3.12, (r/s).rightBound());
  EXPECT_GE(3.12/3.14, (r/r).leftBound());
  EXPECT_LE(3.14/3.12, (r/r).rightBound());
  r = r / r;
  EXPECT_GE(3.12/3.14, r.leftBound());
  EXPECT_LE(3.14/3.12, r.rightBound());

  DInterval t(-0.1, -1e-50), u(t);
  EXPECT_GE(1e-49, (t/u).leftBound());
  EXPECT_LE(1e49, (t/u).rightBound());
  EXPECT_GE(1e-49, (t/t).leftBound());
  EXPECT_LE(1e49, (t/t).rightBound());
  t = t / t;
  EXPECT_GE(1e-49, t.leftBound());
  EXPECT_LE(1e49, t.rightBound());

  DInterval w(-150, -50), x(w);
  EXPECT_GE(1.0/3, (w/x).leftBound());
  EXPECT_LE(3, (w/x).rightBound());
  EXPECT_GE(1.0/3, (w/w).leftBound());
  EXPECT_LE(3, (w/w).rightBound());
  w = w / w;
  EXPECT_GE(1.0/3, w.leftBound());
  EXPECT_LE(3, w.rightBound());

  DInterval y(16,23), z(y);
  EXPECT_GE(16.0/23.0, (y/z).leftBound());
  EXPECT_LE(23.0/16.0, (y/z).rightBound());
  EXPECT_GE(16.0/23.0, (y/y).leftBound());
  EXPECT_LE(23.0/16.0, (y/y).rightBound());
  y = y / y;
  EXPECT_GE(16.0/23.0, y.leftBound());
  EXPECT_LE(23.0/16.0, y.rightBound());
}

TEST_F(FIXTURE_NAME, divisionAndAssignmentOpetator) {
  DInterval result;
  DInterval a(0.001, 0.01);
  a /= a;
  EXPECT_GE(0.1, a.leftBound());
  EXPECT_LE(10, a.rightBound());

  DInterval b(-0.01, -0.001);
  b /= b;
  EXPECT_GE(0.1, b.leftBound());
  EXPECT_LE(10, b.rightBound());

  DInterval c(-0.1, 0.1), c1(1e-100, 0.1);
  EXPECT_THROW(b / c, capd::intervals::IntervalError<double>);
  c /= c1;
  EXPECT_GE(-1e99, c.leftBound());
  EXPECT_LE(1e99, c.rightBound());

  DInterval d(-1.1, 1.1), d1(-1.1, -0.5);
  d /= d1;
  EXPECT_GE(-2.2, d.leftBound());
  EXPECT_LE(2.2, d.rightBound());

  DInterval e(0.11,2),f(-1, 3), f1(0.12,3);
  result = f;
  result /= e;
  EXPECT_GE(-1/0.11, result.leftBound());
  EXPECT_LE(3/0.11, result.rightBound());
  result = e;
  result /= f1;
  EXPECT_GE(0.11/3, result.leftBound());
  EXPECT_LE(2/0.12, result.rightBound());
  result = f1;
  result /= e;
  EXPECT_GE(0.06, result.leftBound());
  EXPECT_LE(3/0.11, result.rightBound());

  e = DInterval(-2, -0.17);
  f = DInterval(-3, 1);
  f1 = DInterval(-3,-0.12);
  result = f;
  result /= e;
  EXPECT_GE(1/-0.17, result.leftBound());
  EXPECT_LE(-3/-0.17, result.rightBound());
  result = e;
  result /= f1;
  EXPECT_GE(0.17/3, result.leftBound());
  EXPECT_LE(2/0.12, result.rightBound());
  result = f1;
  result /= e;
  EXPECT_GE(0.12/2, result.leftBound());
  EXPECT_LE(3/0.17, result.rightBound());

  DInterval g(-15, -11), h(0.1,12);
  result = g;
  result /= h;
  EXPECT_GE(-15/0.1, result.leftBound());
  EXPECT_LE(-11.0/12.0, result.rightBound());
  result = h;
  result /= g;
  EXPECT_GE(-12.0/-11.0, result.leftBound());
  EXPECT_LE(-0.1/15, result.rightBound());

  DInterval i(-1000, 10), j(10, 15);
  result = i;
  result /= j;
  EXPECT_GE(-100, result.leftBound());
  EXPECT_LE(1, result.rightBound());

  DInterval i1(-1000, -10), j1(-10, -5);
  result = i1;
  result /= j1;
  EXPECT_GE(1, result.leftBound());
  EXPECT_LE(200, result.rightBound());
  result = j1;
  result /= i1;
  EXPECT_GE(5e-3, result.leftBound());
  EXPECT_LE(1, result.rightBound());

  DInterval i2(-14.1, -0.3), j2(-0.3, 12.21);
  result = j2;
  result /= i2;
  EXPECT_GE(-12.21/0.3, result.leftBound());
  EXPECT_LE(1, result.rightBound());

  DInterval i3(-11.1, -10.1), j3(-10.1, -10);
  result = i3;
  result /= j3;
  EXPECT_GE(1, result.leftBound());
  EXPECT_LE(1.11, result.rightBound());
  result = j3;
  result /= i3;
  EXPECT_GE(10/11.1, result.leftBound());
  EXPECT_LE(1, result.rightBound());

  DInterval i4(0.01, 0.1), j4(0.1, 1.1);
  result = i4;
  result /= j4;
  EXPECT_GE(1.0/110, result.leftBound());
  EXPECT_LE(1, result.rightBound());
  result = j4;
  result /= i4;
  EXPECT_GE(1, result.leftBound());
  EXPECT_LE(110, result.rightBound());

  DInterval i5(0.1, 3.15), j5(3.15, 32);
  result = i5;
  result /= j5;
  EXPECT_GE(0.1/32, result.leftBound());
  EXPECT_LE(1, result.rightBound());
  result = j5;
  result /= i5;
  EXPECT_GE(1, result.leftBound());
  EXPECT_LE(320, result.rightBound());

  DInterval k(-15, -5), l(-1, 5);
  result = l;
  result /= k;
  EXPECT_GE(-1, result.leftBound());
  EXPECT_LE(0.2, result.rightBound());

  DInterval k1(-15, -5), l1(1, 5);
  result = k1;
  result /= l1;
  EXPECT_GE(-15, result.leftBound());
  EXPECT_LE(-1, result.rightBound());
  result = l1;
  result /= k1;
  EXPECT_GE(-1, result.leftBound());
  EXPECT_LE(-1.0/15.0, result.rightBound());

  DInterval m(1,5), n(3,8);
  result = m;
  result /= n;
  EXPECT_GE(1.0/8.0, result.leftBound());
  EXPECT_LE(5.0/3.0, result.rightBound());
  result = n;
  result /= m;
  EXPECT_GE(3.0/5.0, result.leftBound());
  EXPECT_LE(8, result.rightBound());

  DInterval o(-1,15), p(0.01,12);
  result = o;
  result /= p;
  EXPECT_GE(-100, result.leftBound());
  EXPECT_LE(1500, result.rightBound());

  DInterval q(10000, 5000000), q1(q);
  result = q;
  result /= q1;
  EXPECT_GE(1.0/500, result.leftBound());
  EXPECT_LE(500, result.rightBound());
  result = q;
  result /= q;
  EXPECT_GE(1.0/500, result.leftBound());
  EXPECT_LE(500, result.rightBound());
  result = q;
  result /= result;
  EXPECT_GE(1.0/500, result.leftBound());
  EXPECT_LE(500, result.rightBound());

  DInterval r(-3.14, -3.12), s(r);
  result = r;
  result /= s;
  EXPECT_GE(3.12/3.14, result.leftBound());
  EXPECT_LE(3.14/3.12, result.rightBound());
  result = r;
  result /= result;
  EXPECT_GE(3.12/3.14, result.leftBound());
  EXPECT_LE(3.14/3.12, result.rightBound());

  DInterval t(-0.1, -1e-50), u(t);
  result = t;
  result /= u;
  EXPECT_GE(1e-49, result.leftBound());
  EXPECT_LE(1e49, result.rightBound());
  result = t;
  result /= result;
  EXPECT_GE(1e-49, result.leftBound());
  EXPECT_LE(1e49, result.rightBound());

  DInterval w(-150, -50), x(w);
  result = w;
  result /= x;
  EXPECT_GE(1.0/3, result.leftBound());
  EXPECT_LE(3, result.rightBound());
  result = w;
  result /= result;
  EXPECT_GE(1.0/3, result.leftBound());
  EXPECT_LE(3, result.rightBound());

  DInterval y(16,23), z(y);
  result = y;
  result /= z;
  EXPECT_GE(16.0/23.0, result.leftBound());
  EXPECT_LE(23.0/16.0, result.rightBound());
  result = y;
  result /= result;
  EXPECT_GE(16.0/23.0, result.leftBound());
  EXPECT_LE(23.0/16.0, result.rightBound());
}

TEST_F(FIXTURE_NAME, powerOpetator) {
  DInterval a(-3.323, 1e-100);
  EXPECT_THROW(a^-1, capd::intervals::IntervalError<double>);

  DInterval b(-2.234), c(0), d(9932);
  EXPECT_EQ(1, b^0);
  EXPECT_THROW(c^0, capd::intervals::IntervalError<double>);
  EXPECT_EQ(1, d^0);

  DInterval e(-1.11, -1e-100), f(-3.12, 0), g(-1.11, 1.e-100), h(0, 0.0784), i(1e-100, 743.333);
  EXPECT_EQ(DInterval(1), e^0);
  EXPECT_THROW( f^0, capd::intervals::IntervalError<double>);
  EXPECT_THROW( g^0, capd::intervals::IntervalError<double>);
  EXPECT_THROW( h^0, capd::intervals::IntervalError<double>);
  EXPECT_EQ(DInterval(1), i^0);

  DInterval j(0, 0.1);
  j = j^100;
  EXPECT_GE(0, j.leftBound());
  EXPECT_LE(1e-100, j.rightBound());
  EXPECT_THROW(j^-1, capd::intervals::IntervalError<double>);

  DInterval k(0.001, 2);
  k = k^10;
  EXPECT_GE(1e-30, k.leftBound());
  EXPECT_LE(1024, k.rightBound());

  DInterval l(-0.1, 0.1);
  EXPECT_GE(0, (l^2).leftBound());
  EXPECT_LE(0.01, (l^2).rightBound());

  EXPECT_GE(-0.001, (l^3).leftBound());
  EXPECT_LE(0.001, (l^3).rightBound());

  DInterval m(-4, -0.3);
  EXPECT_GE(0.09, (m^2).leftBound());
  EXPECT_LE(16, (m^2).rightBound());

  EXPECT_GE(-64, (m^3).leftBound());
  EXPECT_LE(-0.027, (m^3).rightBound());

  DInterval n(-0.3, 0);
  EXPECT_GE(0, (n^2).leftBound());
  EXPECT_LE(0.09, (n^2).rightBound());

  EXPECT_GE(-0.027, (n^3).leftBound());
  EXPECT_LE(0, (n^3).rightBound());
  ///EXPECT_THROW(n^-1, capd::intervals::IntervalError<double>);

  DInterval o(0,1);
  EXPECT_EQ(o, o^1000000);

  DInterval p(-1,1);
  EXPECT_EQ(o,p^1000000);
  EXPECT_EQ(p,p^1000001);

  DInterval q(-1,0);
  EXPECT_EQ(o, q^1000000);
  EXPECT_EQ(q, q^1000001);

  DInterval r(-7, -1);
  EXPECT_EQ(-1, (r^-1).leftBound());
  EXPECT_EQ(-1.0/7.0, (r^-1).rightBound());
  EXPECT_EQ(1.0/49.0, (r^-2).leftBound());
  EXPECT_EQ(1, (r^-2).rightBound());
  EXPECT_EQ(-1, (r^-3).leftBound());
  EXPECT_EQ(-1.0/343, (r^-3).rightBound());

  DInterval s(1.7, 3);
  EXPECT_EQ(1.0/3.0, (s^-1).leftBound());
  EXPECT_EQ(1.0/1.7, (s^-1).rightBound());
  EXPECT_EQ(1.0/9.0, (s^-2).leftBound());
  EXPECT_LE(1.0/(1.7*1.7), (s^-2).rightBound());
  EXPECT_EQ(1.0/27.0, (s^-3).leftBound());
  EXPECT_LE(1.0/(1.7*1.7*1.7), (s^-3).rightBound());

  DInterval w(-3, -1.7);
  EXPECT_EQ(-1.0/1.7, (w^-1).leftBound());
  EXPECT_EQ(-1.0/3.0, (w^-1).rightBound());
  EXPECT_EQ(1.0/9.0, (w^-2).leftBound());
  EXPECT_LE(1.0/(1.7*1.7), (w^-2).rightBound());
  EXPECT_GE(-1.0/(1.7*1.7*1.7), (w^-3).leftBound());
  EXPECT_EQ(-1.0/27.0, (w^-3).rightBound());

  DInterval t(-1), u(1);
  EXPECT_EQ(u, (t^-1000000));
  EXPECT_EQ(t, (t^-1000001));
  EXPECT_EQ(u, (u^-1000000));
  EXPECT_EQ(u, (u^-1000001));
}

double compute_sin_error(DInterval z)
{

	 DInterval sinintv=sin(z);
	 double dsin=sin(z.rightBound());
	 return (capd::abs(sinintv - dsin)).rightBound();
}

TEST_F(FIXTURE_NAME, sin) {
    double expectedError = 1.0e-15;
	EXPECT_GE(expectedError, compute_sin_error(DInterval::pi()));
	EXPECT_GE(expectedError, compute_sin_error(6.0));
	EXPECT_GE(expectedError, compute_sin_error(1.0));
}
#endif
