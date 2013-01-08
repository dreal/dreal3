/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file TaylorException.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_DYNSYS_TAYLOREXCEPTION_H_ 
#define _CAPD_DYNSYS_TAYLOREXCEPTION_H_ 

#include <string>
#include <sstream>
#include <fstream>
#include <stdexcept>

namespace capd{
namespace dynsys{

template<typename VectorType>
class TaylorException : public std::runtime_error{
public:
  typedef typename VectorType::ScalarType ScalarType;

  VectorType V;
  ScalarType step;
  std::string message;

  TaylorException(const std::string &info, const VectorType &_V, const ScalarType &S)
    : std::runtime_error(info), V(_V), step(S)
  {
    std::ostringstream d;
    d << std::runtime_error::what() << "\n";
    d << "the set: " << V << "\n";
    d << "time step: " << step << "\n";
    message = d.str();
  }

  ~TaylorException() throw() {}

  const char* what() const throw()
  {
    return message.c_str();
  }
};

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_TAYLOREXCEPTION_H_ 

/// @}
