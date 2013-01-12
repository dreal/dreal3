/*
 * PpedSetTest.cpp
 *
 *  Created on: Oct 16, 2009
 *      Author: kapela
 */

#ifndef _UNITTESTS_PPEDSETTEST_CPP_
#define _UNITTESTS_PPEDSETTEST_CPP_

#include "capd/capdlib.h"
#include "capd/dynset/C0PpedSet.hpp"

template class capd::dynset::C0PpedSet<capd::IMatrix>;
typedef capd::dynset::C0PpedSet<capd::IMatrix> SetType;

#define FIXTURE_NAME C0PpedSetTest
#include "AffineSetCommonTest.hpp"
#include "CenteredAffineSetSpecific.hpp"

#endif
