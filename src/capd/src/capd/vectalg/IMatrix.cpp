
/////////////////////////////////////////////////////////////////////////////
/// @file IMatrix.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include "capd/interval/lib.h"
#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"

namespace capd{ 
  namespace vectalg{


template class Matrix<Interval,DIM,DIM>;
template class RowVector<Interval,DIM>;
template class ColumnVector<Interval,DIM>;

template Matrix<Interval,DIM,DIM> abs <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&);
template Matrix<Interval,DIM,DIM> operator- <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&);
template Matrix<Interval,DIM,DIM> operator+ <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Matrix<Interval,DIM,DIM>&);
template Matrix<Interval,DIM,DIM> operator- <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Matrix<Interval,DIM,DIM>&);
template Matrix<Interval,DIM,DIM> operator* <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Matrix<Interval,DIM,DIM>&);
template Vector<Interval,DIM> operator* <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Vector<Interval,DIM>&);
template Matrix<Interval,DIM,DIM> operator* <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Interval&);
template Matrix<Interval,DIM,DIM> operator* <Interval,DIM,DIM> (const Interval&, const Matrix<Interval,DIM,DIM>&);
template Matrix<Interval,DIM,DIM> operator/ <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Interval&);
template Matrix<Interval,DIM,DIM> operator+ <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Interval&);
template Matrix<Interval,DIM,DIM> operator- <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Interval&);
template bool operator< <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Matrix<Interval,DIM,DIM>&);
template bool operator> <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Matrix<Interval,DIM,DIM>&);
template bool operator<= <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Matrix<Interval,DIM,DIM>&);
template bool operator>= <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&, const Matrix<Interval,DIM,DIM>&);
template Matrix<Interval,DIM,DIM> Transpose <Interval,DIM,DIM> (const Matrix<Interval,DIM,DIM>&);
template std::ostream &operator<< <Interval,DIM,DIM> (std::ostream&, const Matrix<Interval,DIM,DIM>&);
template std::istream &operator>> <Interval,DIM,DIM> (std::istream&, Matrix<Interval,DIM,DIM>&);

// intervalMatrix

typedef Matrix<Interval,DIM,DIM> IMatrix;
template void split<IMatrix>(IMatrix&, IMatrix&);
template IMatrix midMatrix<IMatrix>(const IMatrix&);
template bool intersection<IMatrix>(const IMatrix&,const IMatrix&, IMatrix&);


// RowVector

template Vector<Interval,DIM> operator+<Interval,DIM>(
      const Vector<Interval,DIM>&,
      const RowVector<Interval,DIM>&
   );
template Vector<Interval,DIM> operator+<Interval,DIM>(
      const RowVector<Interval,DIM>&,
      const Vector<Interval,DIM>&
   );
template Vector<Interval,DIM> operator+<Interval,DIM>(
      const RowVector<Interval,DIM>&,
      const RowVector<Interval,DIM>&
   );

template Vector<Interval,DIM> operator-<Interval,DIM>(
      const Vector<Interval,DIM>&,
      const RowVector<Interval,DIM>&
   );
template Vector<Interval,DIM> operator-<Interval,DIM>(
      const RowVector<Interval,DIM>&,
      const Vector<Interval,DIM>&
   );
template Vector<Interval,DIM> operator-<Interval,DIM>(
      const RowVector<Interval,DIM>&,
      const RowVector<Interval,DIM>&
   );

template Interval operator*<Interval,DIM>(
      const Vector<Interval,DIM>&,
      const RowVector<Interval,DIM>&
   );
template Interval operator*<Interval,DIM>(
      const RowVector<Interval,DIM>&,
      const Vector<Interval,DIM>&
   );
template Interval operator*<Interval,DIM>(
      const RowVector<Interval,DIM>&,
      const RowVector<Interval,DIM>&
   );

template Vector<Interval,DIM> operator-<Interval,DIM>(const RowVector<Interval,DIM>&);
template Vector<Interval,DIM> operator*<Interval,DIM,DIM>(
      const Matrix<Interval,DIM,DIM>&, const RowVector<Interval,DIM>&
   );

template Vector<Interval,DIM> operator*<Interval,DIM>(const Interval&, const RowVector<Interval,DIM>&);
template Vector<Interval,DIM> operator*<Interval,DIM>(const RowVector<Interval,DIM>&, const Interval&);
template Vector<Interval,DIM> operator/<Interval,DIM>(const RowVector<Interval,DIM>&, const Interval&);

template std::ostream& operator<< <Interval,DIM>(std::ostream&, const RowVector<Interval,DIM>&);


// ColumnVector

template Vector<Interval,DIM> operator+<Interval,DIM>(
      const Vector<Interval,DIM>&,
      const ColumnVector<Interval,DIM>&
   );
template Vector<Interval,DIM> operator+<Interval,DIM>(
      const ColumnVector<Interval,DIM>&,
      const Vector<Interval,DIM>&
   );
template Vector<Interval,DIM> operator+<Interval,DIM>(
      const ColumnVector<Interval,DIM>&,
      const ColumnVector<Interval,DIM>&
   );

template Vector<Interval,DIM> operator-<Interval,DIM>(
      const Vector<Interval,DIM>&,
      const ColumnVector<Interval,DIM>&
   );
template Vector<Interval,DIM> operator-<Interval,DIM>(
      const ColumnVector<Interval,DIM>&,
      const Vector<Interval,DIM>&
   );
template Vector<Interval,DIM> operator-<Interval,DIM>(
      const ColumnVector<Interval,DIM>&,
      const ColumnVector<Interval,DIM>&
   );

template Interval operator*<Interval,DIM>(
      const Vector<Interval,DIM>&,
      const ColumnVector<Interval,DIM>&
   );
template Interval operator*<Interval,DIM>(
      const ColumnVector<Interval,DIM>&,
      const Vector<Interval,DIM>&
   );
template Interval operator*<Interval,DIM>(
      const ColumnVector<Interval,DIM>&,
      const ColumnVector<Interval,DIM>&
   );

template Vector<Interval,DIM> operator-<Interval,DIM>(const ColumnVector<Interval,DIM>&);
template Vector<Interval,DIM> operator*<Interval,DIM,DIM>(
      const Matrix<Interval,DIM,DIM>&,
      const ColumnVector<Interval,DIM>&
   );

template Vector<Interval,DIM> operator*<Interval,DIM>(const Interval&, const ColumnVector<Interval,DIM>&);
template Vector<Interval,DIM> operator*<Interval,DIM>(const ColumnVector<Interval,DIM>&, const Interval&);
template Vector<Interval,DIM> operator/<Interval,DIM>(const ColumnVector<Interval,DIM>&, const Interval&);

template std::ostream& operator<< <Interval,DIM>(std::ostream&, const ColumnVector<Interval,DIM>&);

}}  // end of namespace capd::vectalg


