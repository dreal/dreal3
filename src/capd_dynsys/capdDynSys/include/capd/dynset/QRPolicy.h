//////////////////////////////////////////////////////////////////////////////// @file QRPolicy.h////// @author Daniel Wilczak/////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2000-2005 by the CAPD Group.//// This file constitutes a part of the CAPD library,// distributed under the terms of the GNU General Public License.// Consult  http://capd.ii.uj.edu.pl/ for details.
#include "capd/vectalg/iobject.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

#ifndef _CAPD_DYNSET_QRPOLICY_H_#define _CAPD_DYNSET_QRPOLICY_H_
namespace capd{namespace dynset{
class FullQRWithPivoting{public:  template<class VectorT, class MatrixT>  static void orthonormalize(MatrixT& B, const VectorT& v)  {    capd::matrixAlgorithms::orthonormalize(B,v);  }
  template<class MatrixT>  static void orthonormalize(MatrixT& B)  {    capd::matrixAlgorithms::orthonormalize(B);  }};
template<int N>class PartialQRWithPivoting{public:  template<class MatrixT>  static void reduceMatrix(MatrixT& B)  {    for(int i=N+1;i<=B.numberOfColumns();++i)      for(int j=1;j<i;++j)        B(j,i)= typename MatrixT::ScalarType(0.);  }  template<class VectorT, class MatrixT>  static void orthonormalize(MatrixT& B, const VectorT& v)  {    reduceMatrix(B);    capd::matrixAlgorithms::orthonormalize(B,v);  }  template<class MatrixT>  static void orthonormalize(MatrixT& B)  {    reduceMatrix(B);    capd::matrixAlgorithms::orthonormalize(B);  }};
class IdQRPolicy{public:  template<class VectorT, class MatrixT>  static void orthonormalize(MatrixT& B, const VectorT& v)  {    B.setToIdentity();  }
  template<class MatrixT>  static void orthonormalize(MatrixT& B)  {    B.setToIdentity();  }};class SelectedQRWithPivoting{public:  template<class VectorT, class MatrixT>  static void orthonormalize(MatrixT& B, const VectorT& v, typename MatrixT::ScalarType level = 1.0e-15)  {    typedef MatrixT MatrixType;    typedef typename MatrixType::RowVectorType VectorType;    typedef typename MatrixType::ScalarType ScalarType;    typedef typename VectorType::template rebind<int>::other IntVectorType;    typedef typename MatrixType::RefColumnVectorType ColumnVectorType;    int dim = v.dimension();    VectorType sizes(dim);    IntVectorType p(dim);    MatrixType Q(dim, dim), R(dim, dim);    capd::matrixAlgorithms::QRdecomposeWithPivoting(B, v, Q, R, sizes, p);  //  std::cout << "\n B " << B << "\n Q = " << Q << "\n sizes " << sizes << "\n p " << p << std::endl;    for(int i=0; i<dim; i++){      if(sizes[i]<=level){        std::cout << "replacing column " << i << "  size is " << sizes[i] << std::endl;        B.column(i) = Q.column(i);      }      else        std::cout << "size is " << sizes[i] << std::endl;    }  }  template<class MatrixT>  static void orthonormalize(MatrixT& B)  {     throw std::runtime_error("NOT IMPLEMENTED METHOD!");  }  template<class MatrixT>  static MatrixT invertMatrix(const MatrixT & B){    return capd::matrixAlgorithms::gaussInverseMatrix(B);  }};
}} // namespace capd::dynset

#endif // _CAPD_DYNSET_QRPOLICY_H_

/// @}
