//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file vectalg/mplib.h
///
/// @author Tomasz Kapela   @date 2010-01-22
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_VECTALG_MPVECTALGLIB_H_
#define _CAPD_VECTALG_MPVECTALGLIB_H_

#include "capd/multiPrec/mplib.h"
#include "capd/intervals/mplib.h"

#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/Matrix.h"
#include "capd/vectalg/Norm.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"

#ifdef __HAVE_MPFR__

namespace capd{

  typedef capd::vectalg::Vector<MpInt,CAPD_DEFAULT_DIMENSION> MpZVector;
  typedef capd::vectalg::Vector<MpFloat,CAPD_DEFAULT_DIMENSION> MpVector;
  typedef capd::vectalg::Vector<MpInterval,CAPD_DEFAULT_DIMENSION> MpIVector;

  typedef capd::vectalg::Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> MpZMatrix;
  typedef capd::vectalg::Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> MpMatrix;
  typedef capd::vectalg::Matrix<MpInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> MpIMatrix;


  typedef capd::vectalg::Norm<MpVector,MpMatrix> MpNorm;
  typedef capd::vectalg::EuclNorm<MpVector,MpMatrix> MpEuclNorm;
  typedef capd::vectalg::MaxNorm<MpVector,MpMatrix> MpMaxNorm;
  typedef capd::vectalg::SumNorm<MpVector,MpMatrix> MpSumNorm;
  typedef capd::vectalg::EuclLNorm<MpVector,MpMatrix> MpEuclLNorm;
  typedef capd::vectalg::MaxLNorm<MpVector,MpMatrix> MpMaxLNorm;
  typedef capd::vectalg::SumLNorm<MpVector,MpMatrix> MpSumLNorm;

  typedef capd::vectalg::Norm<MpIVector,MpIMatrix> MpINorm;
  typedef capd::vectalg::EuclNorm<MpIVector,MpIMatrix> MpIEuclNorm;
  typedef capd::vectalg::MaxNorm<MpIVector,MpIMatrix> MpIMaxNorm;
  typedef capd::vectalg::SumNorm<MpIVector,MpIMatrix> MpISumNorm;
  typedef capd::vectalg::EuclLNorm<MpIVector,MpIMatrix> MpIEuclLNorm;
  typedef capd::vectalg::MaxLNorm<MpIVector,MpIMatrix> MpIMaxLNorm;
  typedef capd::vectalg::SumLNorm<MpIVector,MpIMatrix> MpISumLNorm;

} // end of namespace capd

#endif // __HAVE_MPFR__

#endif // _CAPD_VECTALG_MPVECTALGLIB_H_

