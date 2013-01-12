/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Parser.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2000-2004 */

#ifndef _CAPD_MAP_PARSER_H_ 
#define _CAPD_MAP_PARSER_H_ 

#include <string>
#include <vector>

namespace capd{
namespace map{

class Parser{
public:
  static size_t parseBrackets(const std::string &e, size_t position = std::string::npos);
  static size_t searchForOperator(const std::string &e, unsigned char op, size_t position = std::string::npos);
  static size_t searchForFunction(const std::string &fun, const std::string &eq);
  static bool searchForFunction(const std::string &fun, const std::string &eq, std::string & params);
  static std::string & removeBrackets(std::string &eq);
  static void splitVariables(const std::string &, const std::string&,std::vector<std::string>& result);
  static bool isConstant(std::string&, double& value);
  /// Converts given text to double (returns true on success)
  static bool stringToDouble(std::string const & text, double & result);
  static void removeWhiteSpaces(std::string & text);
};

}} // namespace capd::map

#endif // _CAPD_MAP_PARSER_H_ 

/// @}
