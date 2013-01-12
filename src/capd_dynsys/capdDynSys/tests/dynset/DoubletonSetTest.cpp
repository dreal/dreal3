/*
 * DoubletonSetTest.cpp
 *
 *  Created on: Oct 16, 2009
 *      Author: kapela
 */

#ifndef _UNITTESTS_DOUBLETONSETTEST_CPP_
#define _UNITTESTS_DOUBLETONSETTEST_CPP_
#include "capd/capdlib.h"
#include "capd/geomset/DoubletonSet.hpp"

template class capd::geomset::DoubletonSet<capd::IMatrix>;
typedef capd::geomset::DoubletonSet<capd::IMatrix> SetType;

#define FIXTURE_NAME DoubletonSetTest
#include "AffineSetCommonTest.hpp"

#endif
