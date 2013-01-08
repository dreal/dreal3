/*
 * DoubleRoundingTest.cpp
 *
 *  Created on: Sep 2, 2009
 *      Author: kapela
 */

#include "../gtestHeader.h"
#include "capd/rounding/DoubleRounding.h"

class DoubleRoundingTest: public ::testing::Test {

};


TEST_F(DoubleRoundingTest, roundNearest) {

	 capd::rounding::DoubleRounding::roundNearest();
	 EXPECT_EQ(capd::rounding::RoundNearest, capd::rounding::DoubleRounding::test());
}

TEST_F(DoubleRoundingTest, roundDown) {

	 capd::rounding::DoubleRounding::roundDown();
	 EXPECT_EQ(capd::rounding::RoundDown, capd::rounding::DoubleRounding::test());
}

TEST_F(DoubleRoundingTest, roundUp) {

	 capd::rounding::DoubleRounding::roundUp();
	 EXPECT_EQ(capd::rounding::RoundUp, capd::rounding::DoubleRounding::test());
}

TEST_F(DoubleRoundingTest, roundCut) {

	 capd::rounding::DoubleRounding::roundCut();
	 EXPECT_EQ(capd::rounding::RoundCut, capd::rounding::DoubleRounding::test());
}


TEST_F(DoubleRoundingTest, isWorking) {
	 EXPECT_TRUE(capd::rounding::DoubleRounding::isWorking());
}
