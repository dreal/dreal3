/// @addtogroup capd::vectalg::Matrix<int,0,0>Algorithms
/// @{
/////////////////////////////////////////////////////////////////////////////
/// @file intMatrixAlgorithms.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/capd/minmax.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"
#include <cmath>
namespace capd{
  namespace matrixAlgorithms{

    /* Elementary row and column operations */
template void rowExchange<capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& A,int i,int j);
template void rowMultiply<capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& A,int i,capd::vectalg::Matrix<int,0,0>::ScalarType s);
template void rowAdd<capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& A,int i,int j,capd::vectalg::Matrix<int,0,0>::ScalarType s);
template void columnExchange<capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& A,int i,int j);
template void columnMultiply<capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& A,int j,capd::vectalg::Matrix<int,0,0>::ScalarType s);
template void columnAdd<capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& A,int i,int j,capd::vectalg::Matrix<int,0,0>::ScalarType s);
    /* Elementary row and column operations on capd::vectalg::Matrix<int,0,0> and matrices of bases */
template void rowExchange<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,int i,int j);
template void rowMultiply<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,int i,capd::vectalg::Matrix<int,0,0>::ScalarType q);
template void rowAdd<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,int i,int j,capd::vectalg::Matrix<int,0,0>::ScalarType q);
template void columnExchange<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int i,int j);
template void columnMultiply<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int i,capd::vectalg::Matrix<int,0,0>::ScalarType q);
template void columnAdd<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int i,int j,capd::vectalg::Matrix<int,0,0>::ScalarType q);
            // *** partial reduction *** //
template void partRowReduce<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,int k,int l);
template void partColumnReduce<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int k,int l);
      // *** Test for nonzero matrices *** /
template void smallestNonZero<capd::vectalg::Matrix<int,0,0> >(const capd::vectalg::Matrix<int,0,0>& A,capd::vectalg::Matrix<int,0,0>::ScalarType& s, int& iOpt, int& jOpt);
template bool nonZero<capd::vectalg::Matrix<int,0,0> >(const capd::vectalg::Matrix<int,0,0>& A);
          // *** row echelon form *** //
template void rowPrepare<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,int k,int l);
template void rowReduce<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,int k,int l);
template void rowEchelon<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,int &k);
// *** column echelon form *** //
// *** under construction *** //
template void columnPrepare<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int k,int l);
template void columnReduce<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int k,int l);
template void columnEchelon<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int &l);
// *** Smith diagonalization *** //
template void moveMinNonzero<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int k);
template bool checkForDivisibility<capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,int k,int& i,int& j,capd::vectalg::Matrix<int,0,0>::ScalarType &q);
template void partSmithForm<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int k);
template void smithForm<capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0>,capd::vectalg::Matrix<int,0,0> >(capd::vectalg::Matrix<int,0,0>& B,capd::vectalg::Matrix<int,0,0>& Q,capd::vectalg::Matrix<int,0,0>& Qinv,capd::vectalg::Matrix<int,0,0>& R,capd::vectalg::Matrix<int,0,0>& Rinv,int &s,int &t);
  } // end of namespace matrixAlgorithms
} // end of namespace capd;
/// @}
