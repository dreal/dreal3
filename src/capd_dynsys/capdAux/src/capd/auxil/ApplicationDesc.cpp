/////////////////////////////////////////////////////////////////////////////
/// @file ApplicationDesc.cpp
///
/// @author Mateusz Juda <mateusz.juda@{ii.uj.edu.pl,gmail.com}>
///
/// @date 2013-04-17
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2013 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.edu.pl/ for details. 

#include "capd/auxil/ApplicationDesc.h"

#include <ostream>

using capd::auxil::ApplicationDesc;

namespace capd
{
  namespace auxil
  {
    std::ostream& operator<<(std::ostream& out, const ApplicationDesc& desc)
    {
      out << "Application: " << desc._name << std::endl
	  << " author: " << desc._author << std::endl
	  << " date: " << desc._date << std::endl
	  << " info: " << desc._info << std::endl;
      return out;
    }

  }
}
