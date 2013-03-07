
/////////////////////////////////////////////////////////////////////////////
/// @file mpcapd/vectalg/MpMatrix.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifdef __HAVE_MPFR__

#include "capd/vectalg/mplib.h"
#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/ColumnVector.hpp"
#include "capd/vectalg/RowVector.hpp"
#include "capd/vectalg/Matrix.hpp"

namespace capd{ 
  namespace vectalg{


template class Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>;
template class RowVector<MpInt,CAPD_DEFAULT_DIMENSION>;
template class ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>;

template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> abs <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator+ <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator* <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const MpInt&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const MpInt&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator/ <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const MpInt&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator+ <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const MpInt&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const MpInt&);
template bool operator< <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator> <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator<= <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator>= <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> Transpose <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template std::ostream &operator<< <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (std::ostream&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template std::istream &operator>> <MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (std::istream&, Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);

template void matrixByVector<> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&,Vector<MpInt,CAPD_DEFAULT_DIMENSION>&);
template void matrixByMatrix<> (const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&,Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template void subtractObjects<>(const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v1,const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v2, Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& result);
template void addObjects<>(const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v1,const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v2, Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& result);

// RowVector

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator+<MpInt,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator+<MpInt,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator+<MpInt,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator-<MpInt,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator-<MpInt,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator-<MpInt,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );

template MpInt operator*<MpInt,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template MpInt operator*<MpInt,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template MpInt operator*<MpInt,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator-<MpInt,CAPD_DEFAULT_DIMENSION>(const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator*<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>(
      const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator*<MpInt,CAPD_DEFAULT_DIMENSION>(const MpInt&, const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator*<MpInt,CAPD_DEFAULT_DIMENSION>(const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&, const MpInt&);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator/<MpInt,CAPD_DEFAULT_DIMENSION>(const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&, const MpInt&);

template std::ostream& operator<< <MpInt,CAPD_DEFAULT_DIMENSION>(std::ostream&, const RowVector<MpInt,CAPD_DEFAULT_DIMENSION>&);


// ColumnVector

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator+<MpInt,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator+<MpInt,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator+<MpInt,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator-<MpInt,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator-<MpInt,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator-<MpInt,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );

template MpInt operator*<MpInt,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template MpInt operator*<MpInt,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );
template MpInt operator*<MpInt,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator-<MpInt,CAPD_DEFAULT_DIMENSION>(const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator*<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>(
      const Matrix<MpInt,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator*<MpInt,CAPD_DEFAULT_DIMENSION>(const MpInt&, const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator*<MpInt,CAPD_DEFAULT_DIMENSION>(const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&, const MpInt&);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator/<MpInt,CAPD_DEFAULT_DIMENSION>(const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&, const MpInt&);

template std::ostream& operator<< <MpInt,CAPD_DEFAULT_DIMENSION>(std::ostream&, const ColumnVector<MpInt,CAPD_DEFAULT_DIMENSION>&);


}}  // end of namespace capd::vectalg

#endif // __HAVE_MPFR__
