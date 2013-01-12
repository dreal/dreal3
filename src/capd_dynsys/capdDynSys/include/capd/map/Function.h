/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Function.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_MAP_FUNCTION_H_ 
#define _CAPD_MAP_FUNCTION_H_ 

#include <string>
#include "capd/map/BasicFunction.h"

namespace capd{
namespace map{

/* ________________________ CLASS FUNCTION _______________________*/

template<typename VectorType>
class Function : protected BasicFunction<typename VectorType::ScalarType>
{
public:
  typedef typename VectorType::ScalarType ScalarType;

  Function(const char *, int order = 0); /* constructors */
  Function(const std::string &, int order = 0);
  Function(void);
  Function(const Function &);
  ~Function(void);
  
  const std::string& formula(void) const {return m_fun;}    /* returns the formula as a std::string */
  const std::string& partialDerivative(int i) const;      /* returns partial derivative as a std::string */
  std::string gradient(int) const;
  VectorType gradient(const VectorType &u);
  
  void setParameters(const VectorType & values);
  void setOrder (int order);
  
  Function& operator= (const char *);
  Function& operator= (const std::string &);
  Function& operator= (const Function &);
  
  std::string operator[] (int) const;         /* partial derivative with respect to i-th coordinate 0<=i<dim */
  
  ScalarType operator() (const ScalarType& v) const;         /* for 1-dim function */
  ScalarType operator() (const VectorType &) const ;
  ScalarType operator() (const VectorType &v, int i) const;
  
  using BasicFunction<ScalarType>::setParameter;
  using BasicFunction<ScalarType>::variables;
  using BasicFunction<ScalarType>::dimension;
  using BasicFunction<ScalarType>::differentiateTime;
  using BasicFunction<ScalarType>::setCurrentTime;
  using BasicFunction<ScalarType>::getCurrentTime;
  
protected:
  using BasicFunction<ScalarType>::m_dim;
  using BasicFunction<ScalarType>::m_indexOfFirstParam;
  using BasicFunction<ScalarType>::m_order;
  using BasicFunction<ScalarType>::m_val;
  using BasicFunction<ScalarType>::m_var;
  using BasicFunction<ScalarType>::m_size;
  using BasicFunction<ScalarType>::diffanal;
  using BasicFunction<ScalarType>::eqnanal;
  
  std::string* m_diff; /* the table of partial derivatives */
  std::string m_fun;   /* formula of the function */
  Node<ScalarType>* m_tree;
  Function* m_diffObjects;  
  void createFromText(const std::string &, int);
  void createDefault();
  void createFromObject(const Function &);
  void deleteTables();
  const std::string& currentFormula() {return m_fun;} 
};

}} // the end of the namespace capd::map

#endif // _CAPD_MAP_FUNCTION_H_ 

/// @}
