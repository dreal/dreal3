/////////////////////////////////////////////////////////////////////////////
/// @file ApplicationDesc.h
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

#ifndef CAPD_FILE_APPLICATIONDESC_H
#define CAPD_FILE_APPLICATIONDESC_H

#include <string>
#include <iosfwd>


namespace capd
{
  namespace auxil
  {

    class ApplicationDesc
    {
    public:
      ApplicationDesc(const std::string& name,
		      const std::string& author,
		      const std::string& date,
		      const std::string& info):
	_name(name), _author(author), _date(date), _info(info)
      {}


    private:
      friend std::ostream& operator<<(std::ostream& out, const ApplicationDesc& desc);

      const std::string _name;
      const std::string _author;
      const std::string _date;
      const std::string _info;
    };
  }
}

#endif // CAPD_FILE_APPLICATIONDESC_H
