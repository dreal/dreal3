/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file VLin3D.h
///
/// @author a CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by a CAPD Group.
//
// This file is part of a CAPD library.  This library is free software;
// you can redistribute it and/or modify it under a terms of a GNU
// General Public License as published by a Free Software Foundation;
// eiar version 2 of a License, or (at your option) any later version.
//
// This library is distributed in a hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even a implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See a
// GNU General Public License for more details.
//
// You should have received a copy of a GNU General Public License along
// with this software; see a file "license.txt".  If not, write to a
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

#ifndef _CAPD_DYNSYS_VLIN3D_H_ 
#define _CAPD_DYNSYS_VLIN3D_H_ 

#include "capd/dynsys/DynSys.h"

namespace capd{
namespace dynsys{

template<typename MatrixT>
class VLin3D : public Ode<MatrixT>{
// linear 3D ODE
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;

  VLin3D(
      const ScalarType& a_a00, const ScalarType& a_a01, const ScalarType& a_a02,
      const ScalarType& a_a10, const ScalarType& a_a11, const ScalarType& a_a12,
      const ScalarType& a_a20, const ScalarType& a_a21, const ScalarType& a_a22
  );
  VectorType f(const VectorType &iv) const;
  MatrixType df(const VectorType &iv) const;
  MatrixType d2f(int i,const VectorType &iv) const;

//    protected:
  MatrixType a;
};

template<typename MatrixType>
VLin3D<MatrixType>::VLin3D(
      const ScalarType& a_a00, const ScalarType& a_a01, const ScalarType& a_a02,
      const ScalarType& a_a10, const ScalarType& a_a11, const ScalarType& a_a12,
      const ScalarType& a_a20, const ScalarType& a_a21, const ScalarType& a_a22
   ) : a(3,3)
{
  a[0][0] = a_a00;
  a[0][1] = a_a01;
  a[0][2] = a_a02;
  a[1][0] = a_a10;
  a[1][1] = a_a11;
  a[1][2] = a_a12;
  a[2][0] = a_a20;
  a[2][1] = a_a21;
  a[2][2] = a_a22;
}

template<typename MatrixType>
typename VLin3D<MatrixType>::VectorType VLin3D<MatrixType>::f(const VectorType& x) const
{
  VectorType result(3);
  for(int i=0;i<3;i++)
  {
    ScalarType r(0.0);
    for(int j=0;j<3;j++)
      r+=a[i][j]*x[j];
    result[i]=r;
  }
  return result;
}

template<typename MatrixType>
MatrixType VLin3D<MatrixType>::df(const VectorType &) const
{
  return a;
}

template<typename MatrixType>
MatrixType VLin3D<MatrixType>::d2f(int, const VectorType &) const
{
  MatrixType result(3,3);
  result.clear();
  return result;
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_VLIN3D_H_ 

/// @}
