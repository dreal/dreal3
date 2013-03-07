
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


template class Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>;
template class RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>;
template class ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>;

template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> abs <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator+ <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const MpFloat&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const MpFloat&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator/ <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const MpFloat&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator+ <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const MpFloat&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> operator- <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const MpFloat&);
template bool operator< <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator> <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator<= <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template bool operator>= <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> Transpose <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template std::ostream &operator<< <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (std::ostream&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template std::istream &operator>> <MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> (std::istream&, Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);

template void matrixByVector<> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&,Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&);
template void matrixByMatrix<> (const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&,Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&);
template void subtractObjects<>(const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v1,const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v2, Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& result);
template void addObjects<>(const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v1,const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& v2, Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>& result);


// RowVector

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator+<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator+<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator+<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator-<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator-<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator-<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );

template MpFloat operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template MpFloat operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template MpFloat operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator-<MpFloat,CAPD_DEFAULT_DIMENSION>(const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator*<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>(
      const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&, const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(const MpFloat&, const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&, const MpFloat&);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator/<MpFloat,CAPD_DEFAULT_DIMENSION>(const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&, const MpFloat&);

template std::ostream& operator<< <MpFloat,CAPD_DEFAULT_DIMENSION>(std::ostream&, const RowVector<MpFloat,CAPD_DEFAULT_DIMENSION>&);


// ColumnVector

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator+<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator+<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator+<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator-<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator-<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator-<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );

template MpFloat operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template MpFloat operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );
template MpFloat operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator-<MpFloat,CAPD_DEFAULT_DIMENSION>(const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator*<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>(
      const Matrix<MpFloat,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION>&,
      const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&
   );

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(const MpFloat&, const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator*<MpFloat,CAPD_DEFAULT_DIMENSION>(const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&, const MpFloat&);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator/<MpFloat,CAPD_DEFAULT_DIMENSION>(const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&, const MpFloat&);

template std::ostream& operator<< <MpFloat,CAPD_DEFAULT_DIMENSION>(std::ostream&, const ColumnVector<MpFloat,CAPD_DEFAULT_DIMENSION>&);


}}  // end of namespace capd::vectalg

#endif // __HAVE_MPFR__
