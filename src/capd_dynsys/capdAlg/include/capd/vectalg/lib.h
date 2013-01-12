//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file vectalg/lib.h
///
/// @author Tomasz Kapela   @date 2010-01-23
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_VECTALG_LIB_H_
#define _CAPD_VECTALG_LIB_H_

double power(int val,int ile);
// necessary for the Borland compiler
//#include <math.h>
//inline int sqrt(int x){
//   return ::sqrt(x);
//}
#include "capd/intervals/lib.h"

#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/Matrix.h"
#include "capd/vectalg/Norm.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"
#include "capd/vectalg/Multiindex.h"



namespace capd{
typedef capd::vectalg::Vector<int,DIM> ZVector;

typedef capd::vectalg::Vector<double,DIM> DVector;
typedef capd::vectalg::Matrix<double,DIM,DIM> DMatrix;

typedef capd::vectalg::Vector<Interval,DIM> IVector;
typedef capd::vectalg::Matrix<Interval,DIM,DIM> IMatrix;

typedef capd::vectalg::Norm<DVector,DMatrix> DNorm;
typedef capd::vectalg::EuclNorm<DVector,DMatrix> DEuclNorm;
typedef capd::vectalg::MaxNorm<DVector,DMatrix> DMaxNorm;
typedef capd::vectalg::SumNorm<DVector,DMatrix> DSumNorm;
typedef capd::vectalg::EuclLNorm<DVector,DMatrix> DEuclLNorm;
typedef capd::vectalg::MaxLNorm<DVector,DMatrix> DMaxLNorm;
typedef capd::vectalg::SumLNorm<DVector,DMatrix> DSumLNorm;

typedef capd::vectalg::Norm<IVector,IMatrix> INorm;
typedef capd::vectalg::EuclNorm<IVector,IMatrix> IEuclNorm;
typedef capd::vectalg::MaxNorm<IVector,IMatrix> IMaxNorm;
typedef capd::vectalg::SumNorm<IVector,IMatrix> ISumNorm;
typedef capd::vectalg::EuclLNorm<IVector,IMatrix> IEuclLNorm;
typedef capd::vectalg::MaxLNorm<IVector,IMatrix> IMaxLNorm;
typedef capd::vectalg::SumLNorm<IVector,IMatrix> ISumLNorm;

typedef capd::vectalg::Multiindex Multiindex;
typedef capd::vectalg::Multipointer Multipointer;
} // end of namespace capd

#endif // _CAPD_VECTALG_LIB_H_
