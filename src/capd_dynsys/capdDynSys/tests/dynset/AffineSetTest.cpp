/*
 * commonTests.hpp
 *
 *  Created on: 2009-09-02
 *      Author: iikapela
 */
#ifndef _UNITTESTS_AFFINESETTEST_CPP_
#define _UNITTESTS_AFFINESETTEST_CPP_

#include "capd/capdlib.h"
#include "capd/geomset/AffineSet.hpp"

template class capd::geomset::AffineSet<capd::IMatrix>;
typedef capd::geomset::AffineSet<capd::IMatrix> SetType;

#define FIXTURE_NAME AffineSetTest
#include "AffineSetCommonTest.hpp"
#include "AffineSetSpecific.hpp"
#endif

