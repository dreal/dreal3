
/////////////////////////////////////////////////////////////////////////////
/// @file vectalg/IMatrix.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include "capd/intervals/lib.h"
#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"

namespace capd{ 
  namespace vectalg{


template class Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>;
template class RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>;
template class ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>;

template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> abs <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator+ <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator* <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const capd::DInterval&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const capd::DInterval&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator/ <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const capd::DInterval&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator+ <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const capd::DInterval&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const capd::DInterval&);
template bool operator< <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator> <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator<= <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator>= <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> Transpose <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template std::ostream &operator<< <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (std::ostream&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template std::istream &operator>> <capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (std::istream&, Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);


template void matrixByVector<> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&);
template void matrixByMatrix<> (const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&,Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template void subtractObjects<>(const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v1,const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v2, Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& result);
template void addObjects<>(const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v1,const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v2, Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& result);

// intervalMatrix

typedef Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> IMatrix;
typedef Matrix<capd::DInterval::BoundType,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> DMatrix;
template void split<IMatrix,IMatrix>(IMatrix&, IMatrix&);
template void split<IMatrix,DMatrix>(const IMatrix&, DMatrix&, IMatrix&);
template IMatrix midMatrix<IMatrix>(const IMatrix&);
template bool intersection<IMatrix,IMatrix,IMatrix>(const IMatrix&,const IMatrix&, IMatrix&);


// RowVector

template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator+<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator+<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator+<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator-<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator-<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator-<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );

template capd::DInterval operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template capd::DInterval operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template capd::DInterval operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator-<capd::DInterval,CAPD_DEFAULT_DIMENSION>(const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&);
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>(
      const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(const capd::DInterval&, const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&);
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&, const capd::DInterval&);
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator/<capd::DInterval,CAPD_DEFAULT_DIMENSION>(const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&, const capd::DInterval&);

template std::ostream& operator<< <capd::DInterval,CAPD_DEFAULT_DIMENSION>(std::ostream&, const RowVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&);


// ColumnVector

template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator+<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator+<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator+<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator-<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator-<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator-<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );

template capd::DInterval operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template capd::DInterval operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );
template capd::DInterval operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator-<capd::DInterval,CAPD_DEFAULT_DIMENSION>(const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&);
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>(
      const Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(const capd::DInterval&, const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&);
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator*<capd::DInterval,CAPD_DEFAULT_DIMENSION>(const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&, const capd::DInterval&);
template Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> operator/<capd::DInterval,CAPD_DEFAULT_DIMENSION>(const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&, const capd::DInterval&);

template std::ostream& operator<< <capd::DInterval,CAPD_DEFAULT_DIMENSION>(std::ostream&, const ColumnVector<capd::DInterval,CAPD_DEFAULT_DIMENSION>&);

}}  // end of namespace capd::vectalg


