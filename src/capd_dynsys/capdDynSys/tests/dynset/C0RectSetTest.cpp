/*
 *  Created on: 2009-09-02
 *      Author: iikapela
 */
#ifndef _UNITTESTS_RECTSETTEST_CPP_
#define _UNITTESTS_RECTSETTEST_CPP_

#include "capd/capdlib.h"
#include "capd/dynset/C0RectSet.hpp"

template class capd::dynset::RectSet<capd::IMatrix>;
typedef capd::dynset::C0RectSet<capd::IMatrix> SetType;

#define FIXTURE_NAME RectSetTest
#include "AffineSetCommonTest.hpp"
#include "CenteredAffineSetSpecific.hpp"

#endif
