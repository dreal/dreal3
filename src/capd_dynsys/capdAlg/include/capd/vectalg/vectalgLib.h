/////////////////////////////////////////////////////////////////////////////
/// @file vectalg/vectalgLib.h
///
/// @author The CAPD Group
/// @deprecated
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _CAPD_VECTALG_VECTALGLIB_H_ 
#define _CAPD_VECTALG_VECTALGLIB_H_ 

double power(int val,int ile);
// necessary for the Borland compiler
#include <math.h>
inline int sqrt(int x)
{
   return ::sqrt(x);
}

#include "capd/intervals/DoubleInterval.h"
#include "capd/intervals/LongDoubleInterval.h"
#include "capd/intervals/MpInterval.h"

#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/Matrix.h"
#include "capd/vectalg/Norm.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"

typedef capd::vectalg::Vector<int,DIM> ZVector;
typedef capd::vectalg::Vector<int,0> ZVectorMD;

typedef capd::vectalg::Vector<double,DIM> DVector;
typedef capd::vectalg::Matrix<double,DIM,DIM> DMatrix;
typedef capd::vectalg::Vector<double,0> DVectorMD;
typedef capd::vectalg::Matrix<double,0,0> DMatrixMD;

typedef capd::vectalg::Vector<long double ,DIM> LDVector;
typedef capd::vectalg::Matrix<long double,DIM,DIM> LDMatrix;
typedef capd::vectalg::Vector<long double,0> LDVectorMD;
typedef capd::vectalg::Matrix<long double,0,0> LDMatrixMD;

typedef capd::vectalg::Vector<interval,DIM> IVector;
typedef capd::vectalg::Matrix<interval,DIM,DIM> IMatrix;
typedef capd::vectalg::Vector<interval,0> IVectorMD;
typedef capd::vectalg::Matrix<interval,0,0> IMatrixMD;


typedef capd::vectalg::Norm<DVector,DMatrix> DNorm;
typedef capd::vectalg::EuclNorm<DVector,DMatrix> DEuclNorm;
typedef capd::vectalg::MaxNorm<DVector,DMatrix> DMaxNorm;
typedef capd::vectalg::SumNorm<DVector,DMatrix> DSumNorm;
typedef capd::vectalg::EuclLNorm<DVector,DMatrix> DEuclLNorm;
typedef capd::vectalg::MaxLNorm<DVector,DMatrix> DMaxLNorm;
typedef capd::vectalg::SumLNorm<DVector,DMatrix> DSumLNorm;

typedef capd::vectalg::Norm<LDVector,LDMatrix> LDNorm;
typedef capd::vectalg::EuclNorm<LDVector,LDMatrix> LDEuclNorm;
typedef capd::vectalg::MaxNorm<LDVector,LDMatrix> LDMaxNorm;
typedef capd::vectalg::SumNorm<LDVector,LDMatrix> LDSumNorm;
typedef capd::vectalg::EuclLNorm<LDVector,LDMatrix> LDEuclLNorm;
typedef capd::vectalg::MaxLNorm<LDVector,LDMatrix> LDMaxLNorm;
typedef capd::vectalg::SumLNorm<LDVector,LDMatrix> LDSumLNorm;

typedef capd::vectalg::Norm<IVector,IMatrix> INorm;
typedef capd::vectalg::EuclNorm<IVector,IMatrix> IEuclNorm;
typedef capd::vectalg::MaxNorm<IVector,IMatrix> IMaxNorm;
typedef capd::vectalg::SumNorm<IVector,IMatrix> ISumNorm;
typedef capd::vectalg::EuclLNorm<IVector,IMatrix> IEuclLNorm;
typedef capd::vectalg::MaxLNorm<IVector,IMatrix> IMaxLNorm;
typedef capd::vectalg::SumLNorm<IVector,IMatrix> ISumLNorm;



typedef capd::vectalg::Norm<DVectorMD,DMatrixMD> DNormMD;
typedef capd::vectalg::EuclNorm<DVectorMD,DMatrixMD> DEuclNormMD;
typedef capd::vectalg::MaxNorm<DVectorMD,DMatrixMD> DMaxNormMD;
typedef capd::vectalg::SumNorm<DVectorMD,DMatrixMD> DSumNormMD;
typedef capd::vectalg::EuclLNorm<DVectorMD,DMatrixMD> DEuclLNormMD;
typedef capd::vectalg::MaxLNorm<DVectorMD,DMatrixMD> DMaxLNormMD;
typedef capd::vectalg::SumLNorm<DVectorMD,DMatrixMD> DSumLNormMD;

typedef capd::vectalg::Norm<LDVectorMD,LDMatrixMD> LDNormMD;
typedef capd::vectalg::EuclNorm<LDVectorMD,LDMatrixMD> LDEuclNormMD;
typedef capd::vectalg::MaxNorm<LDVectorMD,LDMatrixMD> LDMaxNormMD;
typedef capd::vectalg::SumNorm<LDVectorMD,LDMatrixMD> LDSumNormMD;
typedef capd::vectalg::EuclLNorm<LDVectorMD,LDMatrixMD> LDEuclLNormMD;
typedef capd::vectalg::MaxLNorm<LDVectorMD,LDMatrixMD> LDMaxLNormMD;
typedef capd::vectalg::SumLNorm<LDVectorMD,LDMatrixMD> LDSumLNormMD;

typedef capd::vectalg::Norm<IVectorMD,IMatrixMD> INormMD;
typedef capd::vectalg::EuclNorm<IVectorMD,IMatrixMD> IEuclNormMD;
typedef capd::vectalg::MaxNorm<IVectorMD,IMatrixMD> IMaxNormMD;
typedef capd::vectalg::SumNorm<IVectorMD,IMatrixMD> ISumNormMD;
typedef capd::vectalg::EuclLNorm<IVectorMD,IMatrixMD> IEuclLNormMD;
typedef capd::vectalg::MaxLNorm<IVectorMD,IMatrixMD> IMaxLNormMD;
typedef capd::vectalg::SumLNorm<IVectorMD,IMatrixMD> ISumLNormMD;




#if (CAPD_CPU_ARCH==CAPD_CPU_ARCH_X86)

  typedef capd::vectalg::Vector<LInterval,DIM> LIVector;
  typedef capd::vectalg::Matrix<LInterval,DIM,DIM> LIMatrix;
  typedef capd::vectalg::Vector<LInterval,0> LIVectorMD;
  typedef capd::vectalg::Matrix<LInterval,0,0> LIMatrixMD;

  typedef capd::vectalg::Norm<LIVector,LIMatrix> LINorm;
  typedef capd::vectalg::EuclNorm<LIVector,LIMatrix> LIEuclNorm;
  typedef capd::vectalg::MaxNorm<LIVector,LIMatrix> LIMaxNorm;
  typedef capd::vectalg::SumNorm<LIVector,LIMatrix> LISumNorm;
  typedef capd::vectalg::EuclLNorm<LIVector,LIMatrix> LIEuclLNorm;
  typedef capd::vectalg::MaxLNorm<LIVector,LIMatrix> LIMaxLNorm;
  typedef capd::vectalg::SumLNorm<LIVector,LIMatrix> LISumLNorm;

  typedef capd::vectalg::Norm<LIVectorMD,LIMatrixMD> LINormMD;
  typedef capd::vectalg::EuclNorm<LIVectorMD,LIMatrixMD> LIEuclNormMD;
  typedef capd::vectalg::MaxNorm<LIVectorMD,LIMatrixMD> LIMaxNormMD;
  typedef capd::vectalg::SumNorm<LIVectorMD,LIMatrixMD> LISumNormMD;
  typedef capd::vectalg::EuclLNorm<LIVectorMD,LIMatrixMD> LIEuclLNormMD;
  typedef capd::vectalg::MaxLNorm<LIVectorMD,LIMatrixMD> LIMaxLNormMD;
  typedef capd::vectalg::SumLNorm<LIVectorMD,LIMatrixMD> LISumLNormMD;

#endif // CAPD_CPU_ARCH==CAPD_CPU_ARCH_X86

#endif // _CAPD_VECTALG_VECTALGLIB_H_ 
