/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicFunction.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2006 */

#ifndef _CAPD_MAP_BASICFUNCTION_H_ 
#define _CAPD_MAP_BASICFUNCTION_H_ 

#include <string>
#include <map>
#include <vector>
#include "capd/map/Node.h"

// This class is a basic for further protected inheritance to classes Function, CnMap  ...
// It should not be use as an independent class

namespace capd{
namespace map{

/* ________________________ CLASS BASICFUNCTION _______________________*/

template<typename Scalar>
class BasicFunction
{
protected:
  typedef Scalar ScalarType;
  typedef Node<ScalarType> NodeType;

  BasicFunction();
  BasicFunction(const BasicFunction&f);
  BasicFunction(const std::string& s, int i);
  BasicFunction(const char* s, int i);
  virtual ~BasicFunction();
   
  void operator=(const BasicFunction&);
  void operator=(const std::string&);
  void operator=(const char* );
   
  int dimension(void) const {return m_dim;}
  void setOrder(int);
  void setParameter(const std::string &name, const ScalarType& value);
  std::string variables() const;
   
  bool depends(std::string, int i) const;
  bool isVariable(std::string&,int i) const;
  int isParam(std::string&) const;
  void eqnanal(std::string&, NodeType **);
  std::string diffanal(std::string&, int i) const;

  void createFromText(std::string s, int i);
  void createFromObject(const BasicFunction& s);
  void createDefault();
  void deleteTables();
  void setCurrentTime(const ScalarType& a_time, int) const;
  void differentiateTime(int) const;
  const ScalarType& getCurrentTime(int) const;
  virtual const std::string& currentFormula()=0;
  template <template <typename T> class NodeT >
  NodeT<ScalarType> * addUnaryNode(std::string & left);
  template <template <typename T> class NodeT >
  NodeT<ScalarType> * addBinaryNode(std::string & left, std::string & right);
  std::vector<std::string> m_var;   /* the table of variables */
  ScalarType* m_val;    /* the table of the values of coordinates */

  int m_dim;   /* dimension of domain */
  int m_indexOfFirstParam; // if equal to m_dim then no parameters specified
  int m_order;
  int m_size;  /* size = dim*order */
  std::map<std::string, NodeType*> m_nodes;
};

}} // the end of the namespace capd::map

#endif // _CAPD_MAP_BASICFUNCTION_H_ 

/// @}
