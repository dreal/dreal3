/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file PoincareException.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file is part of the CAPD library.  This library is free software;
// you can redistribute it and/or modify it under the terms of the GNU
// General Public License as published by the Free Software Foundation;
// either version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this software; see the file "license.txt".  If not, write to the
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

#ifndef _CAPD_POINCARE_POINCARE_EXCEPTION_H_
#define _CAPD_POINCARE_POINCARE_EXCEPTION_H_

#include <string>
#include <sstream>
#include <fstream>
#include <stdexcept>

namespace capd{
namespace poincare{

template<typename setType>
class PoincareException : public std::runtime_error
{
public:
  typedef typename setType::ScalarType ScalarType;
  typedef typename setType::VectorType VectorType;
  typedef setType SetType;

  SetType theSet;
  SetType beforeProblem;

  VectorType enclosure;
  VectorType vectorFieldOnEnclosure;
  VectorType sectionGradientOnEnclosure;

  ScalarType sectionOnEnclosure;
  ScalarType innerProduct;
  std::string message;

  PoincareException(const std::string &info, const SetType &tS, const SetType &bP,
                   const VectorType &enc, const VectorType& fieldOnEnc,
                   const ScalarType &secOnEnc, const VectorType &secGrad,
                   const ScalarType innerP)
    : std::runtime_error(info), theSet(tS), beforeProblem(bP) , enclosure(enc),
      vectorFieldOnEnclosure(fieldOnEnc), sectionGradientOnEnclosure(secGrad), innerProduct(innerP)
  {
    std::ostringstream d;
    d << std::runtime_error::what()<< "\n";
    d << "\nThe set:" << VectorType(theSet);
    d << "\nThe set before problem:" << VectorType(beforeProblem);
    d << "\nComputed enclosure on the set: " << enclosure;
    d << "\nVector field on enclosure: " << vectorFieldOnEnclosure;
    d << "\nSection value on the enclosure: " << sectionOnEnclosure;
    d << "\nSection gradient on the enclosure: " << sectionGradientOnEnclosure;
    d << "\nInner product of vector field and section gradient: " << innerProduct << "\n";
    message = d.str();
  }

  PoincareException(const std::string &info, const SetType &tS, 
                   const ScalarType &sign)
    : std::runtime_error(info), theSet(tS), beforeProblem(tS), sectionOnEnclosure(sign)
  {
    std::ostringstream d;
    d << std::runtime_error::what()<< "\n";
    d << "\nThe set :" << VectorType(theSet);
    d << "\nSection value : " << sectionOnEnclosure << std::ends;
    message = d.str();
  }
  ~PoincareException() throw() {}

  const char * what() const throw()
  {
    return message.c_str();
  }
};

}} // namespace capd::poincare

#endif // _CAPD_POINCARE_POINCARE_EXCEPTION_H_

/// @}
