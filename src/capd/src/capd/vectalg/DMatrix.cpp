
/////////////////////////////////////////////////////////////////////////////
/// @file DMatrix.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/ColumnVector.hpp"
#include "capd/vectalg/RowVector.hpp"
#include "capd/vectalg/Matrix.hpp"

namespace capd{ 
  namespace vectalg{

template class Matrix<double,DIM,DIM>;
template class RowVector<double,DIM>;
template class ColumnVector<double,DIM>;

template Matrix<double,DIM,DIM> abs <double,DIM,DIM> (const Matrix<double,DIM,DIM>&);
template Matrix<double,DIM,DIM> operator- <double,DIM,DIM> (const Matrix<double,DIM,DIM>&);
template Matrix<double,DIM,DIM> operator+ <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const Matrix<double,DIM,DIM>&);
template Matrix<double,DIM,DIM> operator- <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const Matrix<double,DIM,DIM>&);
template Matrix<double,DIM,DIM> operator* <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const Matrix<double,DIM,DIM>&);
template Vector<double,DIM> operator* <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const Vector<double,DIM>&);
template Matrix<double,DIM,DIM> operator* <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const double&);
template Matrix<double,DIM,DIM> operator* <double,DIM,DIM> (const double&, const Matrix<double,DIM,DIM>&);
template Matrix<double,DIM,DIM> operator/ <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const double&);
template Matrix<double,DIM,DIM> operator+ <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const double&);
template Matrix<double,DIM,DIM> operator- <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const double&);
template bool operator< <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const Matrix<double,DIM,DIM>&);
template bool operator> <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const Matrix<double,DIM,DIM>&);
template bool operator<= <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const Matrix<double,DIM,DIM>&);
template bool operator>= <double,DIM,DIM> (const Matrix<double,DIM,DIM>&, const Matrix<double,DIM,DIM>&);
template Matrix<double,DIM,DIM> Transpose <double,DIM,DIM> (const Matrix<double,DIM,DIM>&);
template std::ostream &operator<< <double,DIM,DIM> (std::ostream&, const Matrix<double,DIM,DIM>&);
template std::istream &operator>> <double,DIM,DIM> (std::istream&, Matrix<double,DIM,DIM>&);


// RowVector

template Vector<double,DIM> operator+<double,DIM>(
      const Vector<double,DIM>&,
      const RowVector<double,DIM>&
   );
template Vector<double,DIM> operator+<double,DIM>(
      const RowVector<double,DIM>&,
      const Vector<double,DIM>&
   );
template Vector<double,DIM> operator+<double,DIM>(
      const RowVector<double,DIM>&,
      const RowVector<double,DIM>&
   );

template Vector<double,DIM> operator-<double,DIM>(
      const Vector<double,DIM>&,
      const RowVector<double,DIM>&
   );
template Vector<double,DIM> operator-<double,DIM>(
      const RowVector<double,DIM>&,
      const Vector<double,DIM>&
   );
template Vector<double,DIM> operator-<double,DIM>(
      const RowVector<double,DIM>&,
      const RowVector<double,DIM>&
   );

template double operator*<double,DIM>(
      const Vector<double,DIM>&,
      const RowVector<double,DIM>&
   );
template double operator*<double,DIM>(
      const RowVector<double,DIM>&,
      const Vector<double,DIM>&
   );
template double operator*<double,DIM>(
      const RowVector<double,DIM>&,
      const RowVector<double,DIM>&
   );

template Vector<double,DIM> operator-<double,DIM>(const RowVector<double,DIM>&);
template Vector<double,DIM> operator*<double,DIM,DIM>(
      const Matrix<double,DIM,DIM>&, const RowVector<double,DIM>&
   );

template Vector<double,DIM> operator*<double,DIM>(const double&, const RowVector<double,DIM>&);
template Vector<double,DIM> operator*<double,DIM>(const RowVector<double,DIM>&, const double&);
template Vector<double,DIM> operator/<double,DIM>(const RowVector<double,DIM>&, const double&);

template std::ostream& operator<< <double,DIM>(std::ostream&, const RowVector<double,DIM>&);


// ColumnVector

template Vector<double,DIM> operator+<double,DIM>(
      const Vector<double,DIM>&,
      const ColumnVector<double,DIM>&
   );
template Vector<double,DIM> operator+<double,DIM>(
      const ColumnVector<double,DIM>&,
      const Vector<double,DIM>&
   );
template Vector<double,DIM> operator+<double,DIM>(
      const ColumnVector<double,DIM>&,
      const ColumnVector<double,DIM>&
   );

template Vector<double,DIM> operator-<double,DIM>(
      const Vector<double,DIM>&,
      const ColumnVector<double,DIM>&
   );
template Vector<double,DIM> operator-<double,DIM>(
      const ColumnVector<double,DIM>&,
      const Vector<double,DIM>&
   );
template Vector<double,DIM> operator-<double,DIM>(
      const ColumnVector<double,DIM>&,
      const ColumnVector<double,DIM>&
   );

template double operator*<double,DIM>(
      const Vector<double,DIM>&,
      const ColumnVector<double,DIM>&
   );
template double operator*<double,DIM>(
      const ColumnVector<double,DIM>&,
      const Vector<double,DIM>&
   );
template double operator*<double,DIM>(
      const ColumnVector<double,DIM>&,
      const ColumnVector<double,DIM>&
   );

template Vector<double,DIM> operator-<double,DIM>(const ColumnVector<double,DIM>&);
template Vector<double,DIM> operator*<double,DIM,DIM>(
      const Matrix<double,DIM,DIM>&,
      const ColumnVector<double,DIM>&
   );

template Vector<double,DIM> operator*<double,DIM>(const double&, const ColumnVector<double,DIM>&);
template Vector<double,DIM> operator*<double,DIM>(const ColumnVector<double,DIM>&, const double&);
template Vector<double,DIM> operator/<double,DIM>(const ColumnVector<double,DIM>&, const double&);

template std::ostream& operator<< <double,DIM>(std::ostream&, const ColumnVector<double,DIM>&);

  }}

