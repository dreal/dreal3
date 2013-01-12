//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file lib.h
///
/// @author Tomasz Kapela   @date 2010-01-23
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_ALGLIB_LIB_H_
#define _CAPD_ALGLIB_LIB_H_
#include "capd/matrixAlgorithms/capd2alglib.h"
namespace capd{
  using alglib::complexToString;
  using alglib::computeEigenvalues;
  using alglib::computeEigenvaluesAndEigenvectors;
  using alglib::eigenvaluesToString;
  using alglib::eigenvectorsToString;
} // end of namespace capd

#endif // _CAPD_ALGLIB_LIB_H_
