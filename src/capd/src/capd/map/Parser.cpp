/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Parser.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include <string>
#include <stdexcept>
#include <cstdlib>
#include <iostream>
#include "capd/map/Parser.h"

namespace capd{
  namespace map{

/* _________________________ parseBrackets ____________________________*/

/**
   return a position of '(' which is paired with the last ')'
   or 0, when there are not any parentheses
*/

size_t Parser::parseBrackets(const std::string &e, size_t position)
{
  size_t len = e.find_last_of(')', position);
  if (len==std::string::npos) return 0; //  no parenthese found

  size_t cnt=1;  // contains a difference of the numbers of ')' and '('
  do{
    do{
      if(len==0)
      {
        std::string message = "Parse error in the formula ";
        message += e;
        throw std::runtime_error(message);
      }
      len--;
    }
    while((e.at(len)!='(')&&(e.at(len)!=')'));

    if(e.at(len)==')') cnt++;
    if(e.at(len)=='(')  cnt--;

  }while(cnt);
  return len;
}

/* _________________________ searchForOperator _____________________ */

size_t Parser::searchForOperator(const std::string& e, unsigned char op, size_t position)
/*
   checks if operator <op> appears in text <e> outside any parentheses
   and returns its position
   if not 0 is returned

   the search starts at the end
*/
{
  size_t isOperator = e.find_last_of(op,position);
  if (isOperator == std::string::npos) return 0; // no operator found

  size_t lastBracket = e.find_last_of(')',position);
  if(lastBracket == std::string::npos || isOperator>lastBracket) return isOperator; // no brackets found

  size_t pB = parseBrackets(e,position);
  if(pB) return searchForOperator(e,op,pB-1);
  return 0;
}


/* ________________________ searchForFunction _______________________ */

size_t Parser::searchForFunction(const std::string &fun, const std::string &e)
/**
   returns position of arguments of function <fun> , or
   0 if <fun> does not appear or is an argument for some other function
*/
{
  size_t pos = e.find(fun);
  if(pos || (e.at(fun.size())!='(')) return 0;  // if given fun do not appear or is not on the 0 position
  return parseBrackets(e);
}
/**
 * Checks if \b text begins with \b prefix
 * @param prefix
 * @param text
 * @return true if \b text begins with \b prefix, false otherwise
 */
bool checkPrefix(const std::string & prefix, const std::string & text){
  std::string::const_iterator prefix_it = prefix.begin(),
                              prefix_end = prefix.end(),
                              text_it = text.begin();
  while(prefix_it != prefix_end){
    if(*prefix_it != *text_it)
      return false;
    prefix_it++; text_it++;
  }
  return true;
}
/**
 * Checks if equation is of the form fun(params)
 * @param[in]  fun       function name to be searched for
 * @param[in]  equation  where to search
 * @param[out] params    if equation has form "fun(params)" then on exit it contains "(params)" otherwise is is not changed
 * @return true if equation has correct form, false otherwise
 */
bool Parser::searchForFunction(const std::string &fun, const std::string & equation, std::string & params)
{
  if((!checkPrefix(fun, equation))||(equation.at(fun.size())!='(')) // if given fun do not appear or is not on the 0 position
    return false;
  //TODO : we do not check here that parenthesis are matched properly.
  params=equation.substr(fun.size());
  return true;
}


/* __________________________ removeBrackets ______________________ */

std::string & Parser::removeBrackets(std::string &eq)
/**
  This function removes exterior brackets
*/
{
  while ((!parseBrackets(eq))&&(eq.at(eq.size()-1)==')')){
    eq.erase(eq.size()-1);
    eq.erase(0,1);
  }
  return eq;
}

/*---------------------- splitVariables -----------------------------*/

/*
 This function searches for text 'what' in 'where', then cuts simple words
 separated by: ':' ',' ';' ' ' begining from word next to 'what'.
 The last word is indicated by ';' after that word.
 These words are written to the table tab[].
*/

void Parser::splitVariables(const std::string &what, const std::string &where, std::vector<std::string>& result)
{
  size_t start = where.find(what);
  if(start==std::string::npos)
  {
    std::string message = "Connot find '";
    message += what;
    message += "' in ";
    message += where;
    throw std::runtime_error(message);
  }
  start = where.find_first_of(':',start);
  if(start==std::string::npos)
  {
    std::string message = "Connot find delimiter ':' in ";
    message += where;
    throw std::runtime_error(message);
  }
  size_t last = where.find_first_of(';',start);
  if(last==std::string::npos)
  {
    std::string message = "Connot find delimiter ';' in ";
    message += where;
    throw std::runtime_error(message);
  }

  while(start<last)
  {
    size_t p = where.find_first_of(", :;",start+1);
    if(p==std::string::npos) break;
    result.push_back(where.substr(start+1,p-start-1));
    start=p;
  }
}

/*---------------------- isConstant -----------------------------*/

bool Parser::isConstant(std::string& s, double& value)
{
  removeBrackets(s);
  size_t pos = s.find_first_not_of("0123456789.+-");
  if(pos!=std::string::npos)
    return false;

  pos = s.find_last_of("+-");
  if(pos!=0 && pos!=std::string::npos)
    return false;

  value = std::strtod(s.c_str(),NULL);
  return true;
}

// --- stringToDouble ----------------------------------------------
/**
 * Converts given text to double.
 *
 * @param[in] text double number in the C format
 * @param[out] result on success value of converted text, on failure result is not changed
 * @return true on success, false if given text do not contain correct number or contains some additional characters.
 */
bool Parser::stringToDouble(std::string const & text, double & result) {
    char * endptr;
    char const * strc = text.c_str();

    double d = std::strtod(strc, &endptr);
    if(endptr != strc) {
        while(*endptr && std::isspace(*endptr)) // skip trailing whitespace
           endptr++;
        if(*endptr==0){
          result = d;
          return true;
        }
    }
   return false;
}
/// removes all white spaces from \b text
void Parser::removeWhiteSpaces(std::string & text){
  for(unsigned int i=0; i< text.size(); ++i){
    if(isspace(text[i])){
      text.erase(i,1);
    }
  }
}
}} // namespace capd::map

/// @}
