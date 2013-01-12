
/////////////////////////////////////////////////////////////////////////////
/// @file capd/matrixAlgorithms/floatMatrixAlgorithms.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/auxil/minmax.h"
#include "capd/vectalg/lib.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

using namespace capd;

template void capd::matrixAlgorithms::orthonormalize<DMatrix>(DMatrix&);
template void capd::matrixAlgorithms::QR_decompose<DMatrix>(const DMatrix&,DMatrix&,DMatrix&);
template int capd::matrixAlgorithms::symMatrixDiagonalize<DMatrix>(const DMatrix&,DMatrix&,double);
template double capd::matrixAlgorithms::spectralRadiusOfSymMatrix<DMatrix>(const DMatrix&,double);
template double capd::matrixAlgorithms::maxEigenValueOfSymMatrix<DMatrix>(const DMatrix&,double);
template DVector capd::matrixAlgorithms::gauss<DMatrix,DVector>(const DMatrix&,const DVector&);
template void capd::matrixAlgorithms::croutDecomposition<DMatrix>(const DMatrix&,DMatrix&,DMatrix&);
template DMatrix capd::matrixAlgorithms::invLowerTriangleMatrix<DMatrix>(const DMatrix&);
template DMatrix capd::matrixAlgorithms::invUpperTriangleMatrix<DMatrix>(const DMatrix&);
template DMatrix capd::matrixAlgorithms::inverseMatrix<DMatrix>(const DMatrix&);
template DMatrix capd::matrixAlgorithms::gaussInverseMatrix<DMatrix>(const DMatrix&);

template void capd::matrixAlgorithms::orthonormalize<IMatrix>(IMatrix&);
template void capd::matrixAlgorithms::orthonormalize<IMatrix>(IMatrix&, const IVector&);
template void capd::matrixAlgorithms::QR_decompose<IMatrix>(const IMatrix&,IMatrix&,IMatrix&);
template int capd::matrixAlgorithms::symMatrixDiagonalize<IMatrix>(const IMatrix&,IMatrix&,interval);
template interval capd::matrixAlgorithms::spectralRadiusOfSymMatrix<IMatrix>(const IMatrix&,interval);
template interval capd::matrixAlgorithms:: maxEigenValueOfSymMatrix<IMatrix>(const IMatrix&,interval);
template IVector capd::matrixAlgorithms::gauss<IMatrix,IVector>(const IMatrix&,const IVector&);
template void capd::matrixAlgorithms::croutDecomposition<IMatrix>(const IMatrix&,IMatrix&,IMatrix&);
template IMatrix capd::matrixAlgorithms::invLowerTriangleMatrix<IMatrix>(const IMatrix&);
template IMatrix capd::matrixAlgorithms::invUpperTriangleMatrix<IMatrix>(const IMatrix&);
template IMatrix capd::matrixAlgorithms::inverseMatrix<IMatrix>(const IMatrix&);
template IMatrix capd::matrixAlgorithms::gaussInverseMatrix<IMatrix>(const IMatrix&);
template IMatrix capd::matrixAlgorithms::krawczykInverse<IMatrix>(const IMatrix&);

