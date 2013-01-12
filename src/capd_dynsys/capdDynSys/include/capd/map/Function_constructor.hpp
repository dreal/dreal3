/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Function_constructor.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/*
   Daniel Wilczak, October 2000 - 2004
   This file contains the implementation of constructors, destructor
*/

#ifndef _CAPD_MAP_FUNCTION_CONSTRUCTOR_HPP_ 
#define _CAPD_MAP_FUNCTION_CONSTRUCTOR_HPP_ 

#include <stdexcept>
#include <algorithm>
#include "capd/map/Function.h"

namespace capd{
namespace map{

/*______________________ createDefault ________________________________*/

template<typename VectorType>
void Function<VectorType>::createDefault()
{
  m_diff = new std::string[1];
  m_fun = "0";
  m_diff[0] = "?";
  m_tree = new ConsNode<ScalarType>(m_order,ScalarType(0));
  m_diffObjects = NULL;
}

/*________________________ deleteTables _______________________________*/
template<typename VectorType>
void Function<VectorType>::deleteTables()
{
  delete []m_diff;
  m_diff = 0;
  delete m_tree;
  m_tree = 0; // NULL
  if(m_diffObjects)
    delete [] m_diffObjects;
  m_diffObjects = 0;
}


/*__________________________ CONSTRUCTOR  _____________________________*/

/* This constructor creates a constant function  equal to 0
    with one indefinite variable
*/

template<typename VectorType>
Function<VectorType>::Function(void) 
{
  createDefault();
}

/*__________________________ CONSTRUCTOR  _____________________________*/

/* This constructor reads variables and formula from text parameter */

template<typename VectorType>
Function<VectorType>::Function(const char *s, int i) : BasicFunction<ScalarType>(s,i)
{
  try{
    createFromText(s,i);
  } catch(std::runtime_error &r)
  {
    std::string re = "exception in constructor Function(const char *, int)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
}

/*________________________ COPY CONSTRUCTOR  __________________________*/

template<typename VectorType>
Function<VectorType>::Function(const Function &f) : BasicFunction<ScalarType>(f)
{
  try{
    createFromObject(f);
  } catch(std::runtime_error &r)
  {
    std::string re = "exception in constructor Function(const Function &)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
}

/*__________________________ CONSTRUCTOR  _____________________________*/

template<typename VectorType>
Function<VectorType>::Function(const std::string &f, int i) : BasicFunction<ScalarType>(f,i)
{
  try{
    createFromText(f,i);
  } catch(std::runtime_error &r)
  {
    std::string re = "exception in constructor Function(const string &, int)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
}

/*__________________________ DESTRUCTOR _____________________________*/

/* destructor deletes the dynamic variables: m_tree, stack of the constants
   and possibly stack of IntervalType constants
*/

template<typename VectorType>
Function<VectorType>::~Function(void)
{
  deleteTables();
}

// -----------------------------------------------------------------------------

template<typename VectorType>
void Function<VectorType>::createFromText(const std::string &s, int a_order)
{
  size_t start = s.find(std::string("fun:"));
  size_t last = s.find_first_of(';',start);
  if(last==std::string::npos)
  {
    std::string message("Cannot find delimiter ';' in the formula ");
    throw std::runtime_error(message + s);
  }

  m_fun = s.substr(start+4,last-start-4);  /* we read the formula */
  eqnanal(m_fun,&m_tree);
  
  m_diff = new std::string[m_dim];
  std::fill(m_diff,m_diff+m_dim,"?");
  m_diffObjects = 0;
}

// -----------------------------------------------------------------------------

template<typename VectorType>
void Function<VectorType>::createFromObject(const Function &f)
{
  m_fun = f.m_fun;
  m_diff = new std::string[m_dim];
  
  std::copy(f.m_diff,f.m_diff+m_dim,m_diff);
  
  eqnanal(m_fun,&m_tree);
  m_diffObjects = 0;
}

}} // namespace capd::map

#endif // _CAPD_MAP_FUNCTION_CONSTRUCTOR_HPP_ 

/// @}
