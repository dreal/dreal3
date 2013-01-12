
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


template class Matrix<MpFloat,DIM,DIM>;
template class RowVector<MpFloat,DIM>;
template class ColumnVector<MpFloat,DIM>;

template Matrix<MpFloat,DIM,DIM> abs <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&);
template Matrix<MpFloat,DIM,DIM> operator- <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&);
template Matrix<MpFloat,DIM,DIM> operator+ <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const Matrix<MpFloat,DIM,DIM>&);
template Matrix<MpFloat,DIM,DIM> operator- <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const Matrix<MpFloat,DIM,DIM>&);
template Matrix<MpFloat,DIM,DIM> operator* <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const Matrix<MpFloat,DIM,DIM>&);
template Vector<MpFloat,DIM> operator* <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const Vector<MpFloat,DIM>&);
template Matrix<MpFloat,DIM,DIM> operator* <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const MpFloat&);
template Matrix<MpFloat,DIM,DIM> operator* <MpFloat,DIM,DIM> (const MpFloat&, const Matrix<MpFloat,DIM,DIM>&);
template Matrix<MpFloat,DIM,DIM> operator/ <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const MpFloat&);
template Matrix<MpFloat,DIM,DIM> operator+ <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const MpFloat&);
template Matrix<MpFloat,DIM,DIM> operator- <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const MpFloat&);
template bool operator< <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const Matrix<MpFloat,DIM,DIM>&);
template bool operator> <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const Matrix<MpFloat,DIM,DIM>&);
template bool operator<= <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const Matrix<MpFloat,DIM,DIM>&);
template bool operator>= <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&, const Matrix<MpFloat,DIM,DIM>&);
template Matrix<MpFloat,DIM,DIM> Transpose <MpFloat,DIM,DIM> (const Matrix<MpFloat,DIM,DIM>&);
template std::ostream &operator<< <MpFloat,DIM,DIM> (std::ostream&, const Matrix<MpFloat,DIM,DIM>&);
template std::istream &operator>> <MpFloat,DIM,DIM> (std::istream&, Matrix<MpFloat,DIM,DIM>&);

template void matrixByVector<> (const Matrix<MpFloat,DIM,DIM>&, const Vector<MpFloat,DIM>&,Vector<MpFloat,DIM>&);
template void matrixByMatrix<> (const Matrix<MpFloat,DIM,DIM>&, const Matrix<MpFloat,DIM,DIM>&,Matrix<MpFloat,DIM,DIM>&);
template void subtractObjects<>(const Matrix<MpFloat,DIM,DIM>& v1,const Matrix<MpFloat,DIM,DIM>& v2, Matrix<MpFloat,DIM,DIM>& result);
template void addObjects<>(const Matrix<MpFloat,DIM,DIM>& v1,const Matrix<MpFloat,DIM,DIM>& v2, Matrix<MpFloat,DIM,DIM>& result);


// RowVector

template Vector<MpFloat,DIM> operator+<MpFloat,DIM>(
      const Vector<MpFloat,DIM>&,
      const RowVector<MpFloat,DIM>&
   );
template Vector<MpFloat,DIM> operator+<MpFloat,DIM>(
      const RowVector<MpFloat,DIM>&,
      const Vector<MpFloat,DIM>&
   );
template Vector<MpFloat,DIM> operator+<MpFloat,DIM>(
      const RowVector<MpFloat,DIM>&,
      const RowVector<MpFloat,DIM>&
   );

template Vector<MpFloat,DIM> operator-<MpFloat,DIM>(
      const Vector<MpFloat,DIM>&,
      const RowVector<MpFloat,DIM>&
   );
template Vector<MpFloat,DIM> operator-<MpFloat,DIM>(
      const RowVector<MpFloat,DIM>&,
      const Vector<MpFloat,DIM>&
   );
template Vector<MpFloat,DIM> operator-<MpFloat,DIM>(
      const RowVector<MpFloat,DIM>&,
      const RowVector<MpFloat,DIM>&
   );

template MpFloat operator*<MpFloat,DIM>(
      const Vector<MpFloat,DIM>&,
      const RowVector<MpFloat,DIM>&
   );
template MpFloat operator*<MpFloat,DIM>(
      const RowVector<MpFloat,DIM>&,
      const Vector<MpFloat,DIM>&
   );
template MpFloat operator*<MpFloat,DIM>(
      const RowVector<MpFloat,DIM>&,
      const RowVector<MpFloat,DIM>&
   );

template Vector<MpFloat,DIM> operator-<MpFloat,DIM>(const RowVector<MpFloat,DIM>&);
template Vector<MpFloat,DIM> operator*<MpFloat,DIM,DIM>(
      const Matrix<MpFloat,DIM,DIM>&, const RowVector<MpFloat,DIM>&
   );

template Vector<MpFloat,DIM> operator*<MpFloat,DIM>(const MpFloat&, const RowVector<MpFloat,DIM>&);
template Vector<MpFloat,DIM> operator*<MpFloat,DIM>(const RowVector<MpFloat,DIM>&, const MpFloat&);
template Vector<MpFloat,DIM> operator/<MpFloat,DIM>(const RowVector<MpFloat,DIM>&, const MpFloat&);

template std::ostream& operator<< <MpFloat,DIM>(std::ostream&, const RowVector<MpFloat,DIM>&);


// ColumnVector

template Vector<MpFloat,DIM> operator+<MpFloat,DIM>(
      const Vector<MpFloat,DIM>&,
      const ColumnVector<MpFloat,DIM>&
   );
template Vector<MpFloat,DIM> operator+<MpFloat,DIM>(
      const ColumnVector<MpFloat,DIM>&,
      const Vector<MpFloat,DIM>&
   );
template Vector<MpFloat,DIM> operator+<MpFloat,DIM>(
      const ColumnVector<MpFloat,DIM>&,
      const ColumnVector<MpFloat,DIM>&
   );

template Vector<MpFloat,DIM> operator-<MpFloat,DIM>(
      const Vector<MpFloat,DIM>&,
      const ColumnVector<MpFloat,DIM>&
   );
template Vector<MpFloat,DIM> operator-<MpFloat,DIM>(
      const ColumnVector<MpFloat,DIM>&,
      const Vector<MpFloat,DIM>&
   );
template Vector<MpFloat,DIM> operator-<MpFloat,DIM>(
      const ColumnVector<MpFloat,DIM>&,
      const ColumnVector<MpFloat,DIM>&
   );

template MpFloat operator*<MpFloat,DIM>(
      const Vector<MpFloat,DIM>&,
      const ColumnVector<MpFloat,DIM>&
   );
template MpFloat operator*<MpFloat,DIM>(
      const ColumnVector<MpFloat,DIM>&,
      const Vector<MpFloat,DIM>&
   );
template MpFloat operator*<MpFloat,DIM>(
      const ColumnVector<MpFloat,DIM>&,
      const ColumnVector<MpFloat,DIM>&
   );

template Vector<MpFloat,DIM> operator-<MpFloat,DIM>(const ColumnVector<MpFloat,DIM>&);
template Vector<MpFloat,DIM> operator*<MpFloat,DIM,DIM>(
      const Matrix<MpFloat,DIM,DIM>&,
      const ColumnVector<MpFloat,DIM>&
   );

template Vector<MpFloat,DIM> operator*<MpFloat,DIM>(const MpFloat&, const ColumnVector<MpFloat,DIM>&);
template Vector<MpFloat,DIM> operator*<MpFloat,DIM>(const ColumnVector<MpFloat,DIM>&, const MpFloat&);
template Vector<MpFloat,DIM> operator/<MpFloat,DIM>(const ColumnVector<MpFloat,DIM>&, const MpFloat&);

template std::ostream& operator<< <MpFloat,DIM>(std::ostream&, const ColumnVector<MpFloat,DIM>&);


}}  // end of namespace capd::vectalg

#endif // __HAVE_MPFR__
