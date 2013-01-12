/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Linear3d.h
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

#ifndef _CAPD_DYNSYS_LINEAR3D_H_ 
#define _CAPD_DYNSYS_LINEAR3D_H_ 

#include "capd/dynsys/DynSys.h"

namespace capd{
namespace dynsys{

template<typename MatrixT>
class Linear3d : public DynSys<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;

  Linear3d(const ScalarType& a_a, const ScalarType& a_b, const ScalarType& a_c,
            const ScalarType& a_d, const ScalarType& a_e, const ScalarType& a_f,
            const ScalarType& a_g, const ScalarType& a_h, const ScalarType& a_i
  );
  VectorType Phi(const VectorType &iv) const;
  MatrixType JacPhi(const VectorType &iv) const;
  VectorType Remainder(const VectorType &iv) const;
protected:
  ScalarType a,b,c,d,e,f,g,h,i;
};

// --------------------- inline definitions ---------------------- //

template<typename MatrixType>
inline Linear3d<MatrixType>::Linear3d(
      const ScalarType& a_a, const ScalarType& a_b, const ScalarType& a_c,
      const ScalarType& a_d, const ScalarType& a_e, const ScalarType& a_f,
      const ScalarType& a_g, const ScalarType& a_h, const ScalarType& a_i
   ) : a(a_a), b(a_b), c(a_c),
         d(a_d), e(a_e), f(a_f),
         g(a_g), h(a_h), i(a_i)
{}

template<typename MatrixType>
inline typename Linear3d<MatrixType>::VectorType Linear3d<MatrixType>::Remainder(const VectorType&) const
{
  VectorType result(3);
  result.clear();
  return result;
}


template<typename MatrixType>
typename Linear3d<MatrixType>::VectorType Linear3d<MatrixType>::Phi(const VectorType &iv) const
{
  VectorType result(3);
  result[0] = a*iv[0] + b*iv[1] + c*iv[2];
  result[0] = d*iv[0] + e*iv[1] + f*iv[2];
  result[0] = g*iv[0] + h*iv[1] + i*iv[2];
  return result;
}


template<typename MatrixType>
MatrixType Linear3d<MatrixType>::JacPhi(const VectorType &) const
{
  MatrixType result(3,3);

  result[0][0] = a;
  result[0][1] = b;
  result[0][2] = c;
  result[1][0] = d;
  result[1][1] = e;
  result[1][2] = f;
  result[2][0] = g;
  result[2][1] = h;
  result[2][2] = i;

  return result;
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_LINEAR3D_H_ 

/// @}
