
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


template class Matrix<MpInt,DIM,DIM>;
template class RowVector<MpInt,DIM>;
template class ColumnVector<MpInt,DIM>;

template Matrix<MpInt,DIM,DIM> abs <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&);
template Matrix<MpInt,DIM,DIM> operator- <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&);
template Matrix<MpInt,DIM,DIM> operator+ <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const Matrix<MpInt,DIM,DIM>&);
template Matrix<MpInt,DIM,DIM> operator- <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const Matrix<MpInt,DIM,DIM>&);
template Matrix<MpInt,DIM,DIM> operator* <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const Matrix<MpInt,DIM,DIM>&);
template Vector<MpInt,DIM> operator* <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const Vector<MpInt,DIM>&);
template Matrix<MpInt,DIM,DIM> operator* <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const MpInt&);
template Matrix<MpInt,DIM,DIM> operator* <MpInt,DIM,DIM> (const MpInt&, const Matrix<MpInt,DIM,DIM>&);
template Matrix<MpInt,DIM,DIM> operator/ <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const MpInt&);
template Matrix<MpInt,DIM,DIM> operator+ <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const MpInt&);
template Matrix<MpInt,DIM,DIM> operator- <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const MpInt&);
template bool operator< <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const Matrix<MpInt,DIM,DIM>&);
template bool operator> <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const Matrix<MpInt,DIM,DIM>&);
template bool operator<= <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const Matrix<MpInt,DIM,DIM>&);
template bool operator>= <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&, const Matrix<MpInt,DIM,DIM>&);
template Matrix<MpInt,DIM,DIM> Transpose <MpInt,DIM,DIM> (const Matrix<MpInt,DIM,DIM>&);
template std::ostream &operator<< <MpInt,DIM,DIM> (std::ostream&, const Matrix<MpInt,DIM,DIM>&);
template std::istream &operator>> <MpInt,DIM,DIM> (std::istream&, Matrix<MpInt,DIM,DIM>&);

template void matrixByVector<> (const Matrix<MpInt,DIM,DIM>&, const Vector<MpInt,DIM>&,Vector<MpInt,DIM>&);
template void matrixByMatrix<> (const Matrix<MpInt,DIM,DIM>&, const Matrix<MpInt,DIM,DIM>&,Matrix<MpInt,DIM,DIM>&);
template void subtractObjects<>(const Matrix<MpInt,DIM,DIM>& v1,const Matrix<MpInt,DIM,DIM>& v2, Matrix<MpInt,DIM,DIM>& result);
template void addObjects<>(const Matrix<MpInt,DIM,DIM>& v1,const Matrix<MpInt,DIM,DIM>& v2, Matrix<MpInt,DIM,DIM>& result);

// RowVector

template Vector<MpInt,DIM> operator+<MpInt,DIM>(
      const Vector<MpInt,DIM>&,
      const RowVector<MpInt,DIM>&
   );
template Vector<MpInt,DIM> operator+<MpInt,DIM>(
      const RowVector<MpInt,DIM>&,
      const Vector<MpInt,DIM>&
   );
template Vector<MpInt,DIM> operator+<MpInt,DIM>(
      const RowVector<MpInt,DIM>&,
      const RowVector<MpInt,DIM>&
   );

template Vector<MpInt,DIM> operator-<MpInt,DIM>(
      const Vector<MpInt,DIM>&,
      const RowVector<MpInt,DIM>&
   );
template Vector<MpInt,DIM> operator-<MpInt,DIM>(
      const RowVector<MpInt,DIM>&,
      const Vector<MpInt,DIM>&
   );
template Vector<MpInt,DIM> operator-<MpInt,DIM>(
      const RowVector<MpInt,DIM>&,
      const RowVector<MpInt,DIM>&
   );

template MpInt operator*<MpInt,DIM>(
      const Vector<MpInt,DIM>&,
      const RowVector<MpInt,DIM>&
   );
template MpInt operator*<MpInt,DIM>(
      const RowVector<MpInt,DIM>&,
      const Vector<MpInt,DIM>&
   );
template MpInt operator*<MpInt,DIM>(
      const RowVector<MpInt,DIM>&,
      const RowVector<MpInt,DIM>&
   );

template Vector<MpInt,DIM> operator-<MpInt,DIM>(const RowVector<MpInt,DIM>&);
template Vector<MpInt,DIM> operator*<MpInt,DIM,DIM>(
      const Matrix<MpInt,DIM,DIM>&, const RowVector<MpInt,DIM>&
   );

template Vector<MpInt,DIM> operator*<MpInt,DIM>(const MpInt&, const RowVector<MpInt,DIM>&);
template Vector<MpInt,DIM> operator*<MpInt,DIM>(const RowVector<MpInt,DIM>&, const MpInt&);
template Vector<MpInt,DIM> operator/<MpInt,DIM>(const RowVector<MpInt,DIM>&, const MpInt&);

template std::ostream& operator<< <MpInt,DIM>(std::ostream&, const RowVector<MpInt,DIM>&);


// ColumnVector

template Vector<MpInt,DIM> operator+<MpInt,DIM>(
      const Vector<MpInt,DIM>&,
      const ColumnVector<MpInt,DIM>&
   );
template Vector<MpInt,DIM> operator+<MpInt,DIM>(
      const ColumnVector<MpInt,DIM>&,
      const Vector<MpInt,DIM>&
   );
template Vector<MpInt,DIM> operator+<MpInt,DIM>(
      const ColumnVector<MpInt,DIM>&,
      const ColumnVector<MpInt,DIM>&
   );

template Vector<MpInt,DIM> operator-<MpInt,DIM>(
      const Vector<MpInt,DIM>&,
      const ColumnVector<MpInt,DIM>&
   );
template Vector<MpInt,DIM> operator-<MpInt,DIM>(
      const ColumnVector<MpInt,DIM>&,
      const Vector<MpInt,DIM>&
   );
template Vector<MpInt,DIM> operator-<MpInt,DIM>(
      const ColumnVector<MpInt,DIM>&,
      const ColumnVector<MpInt,DIM>&
   );

template MpInt operator*<MpInt,DIM>(
      const Vector<MpInt,DIM>&,
      const ColumnVector<MpInt,DIM>&
   );
template MpInt operator*<MpInt,DIM>(
      const ColumnVector<MpInt,DIM>&,
      const Vector<MpInt,DIM>&
   );
template MpInt operator*<MpInt,DIM>(
      const ColumnVector<MpInt,DIM>&,
      const ColumnVector<MpInt,DIM>&
   );

template Vector<MpInt,DIM> operator-<MpInt,DIM>(const ColumnVector<MpInt,DIM>&);
template Vector<MpInt,DIM> operator*<MpInt,DIM,DIM>(
      const Matrix<MpInt,DIM,DIM>&,
      const ColumnVector<MpInt,DIM>&
   );

template Vector<MpInt,DIM> operator*<MpInt,DIM>(const MpInt&, const ColumnVector<MpInt,DIM>&);
template Vector<MpInt,DIM> operator*<MpInt,DIM>(const ColumnVector<MpInt,DIM>&, const MpInt&);
template Vector<MpInt,DIM> operator/<MpInt,DIM>(const ColumnVector<MpInt,DIM>&, const MpInt&);

template std::ostream& operator<< <MpInt,DIM>(std::ostream&, const ColumnVector<MpInt,DIM>&);


}}  // end of namespace capd::vectalg

#endif // __HAVE_MPFR__
