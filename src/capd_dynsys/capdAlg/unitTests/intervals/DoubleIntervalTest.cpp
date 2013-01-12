/*
 * DoubleIntervalTest.cpp
 *
 *  Created on: 2009-09-02
 *      Author: iikapela
 */


#include "capd/intervals/Interval.hpp"
#include "capd/rounding/DoubleRounding.h"

typedef capd::intervals::Interval<double, capd::rounding::DoubleRounding> DInterval;
typedef capd::intervals::IntervalError<double> DIntervalError;

#define FIXTURE_NAME DoubleIntervalTest

#include "commonTests.hpp"

