/*
 *  Created on: 2009-09-02
 *      Author: iikapela
 */
#ifndef _UNITTESTS_RECT2SETTEST_CPP_
#define _UNITTESTS_RECT2SETTEST_CPP_

#include "capd/capdlib.h"
#include "capd/dynset/C0Rect2RSet.hpp"

template class capd::dynset::Rect2Set<capd::IMatrix>;
typedef capd::dynset::Rect2Set<capd::IMatrix> SetType;

#define FIXTURE_NAME Rect2SetTest

#include "AffineSetCommonTest.hpp"
#include "CenteredDoubletonSpecific.hpp"


#endif
