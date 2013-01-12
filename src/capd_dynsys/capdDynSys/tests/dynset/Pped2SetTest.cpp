/*
 *  Created on: 2009-09-02
 *      Author: iikapela
 */
#ifndef _UNITTESTS_PPED2SETTEST_CPP_
#define _UNITTESTS_PPED2SETTEST_CPP_

#include "capd/capdlib.h"
#include "capd/dynset/Pped2Set.hpp"

template class capd::dynset::Pped2Set<capd::IMatrix>;
typedef capd::dynset::Pped2Set<capd::IMatrix> SetType;

#define FIXTURE_NAME Pped2SetTest
#include "AffineSetCommonTest.hpp"
#include "CenteredDoubletonSpecific.hpp"

#endif
