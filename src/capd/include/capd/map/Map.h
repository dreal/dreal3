/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Map.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak  2000-2005 */

#ifndef _CAPD_MAP_MAP_H_ 
#define _CAPD_MAP_MAP_H_ 

#include <string>
#include <stdexcept>
#include <sstream>
#include <vector>
#include "capd/map/Function.h"

namespace capd{
/// Functions and Maps
namespace map{

template<typename MatrixT>
class Map
{
public:
  Map(void);
  Map(const std::string &, int order=0);
  Map(const char *, int order=0);
  Map(const Map &);

  Map &operator=(const char *);
  Map &operator=(const std::string &);
  Map &operator=(const Map &);
  virtual ~Map()
  {
    delete []m_fun;
    delete []m_der;
  }

  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename VectorType::ScalarType ScalarType;
  typedef Function<VectorType> FunctionType;

  VectorType operator()(const VectorType &, int = 0) const;
  VectorType operator()(const VectorType &, MatrixType &) const;
  MatrixType operator[](const VectorType &) const;
  const FunctionType &operator()(int) const;

  void variational(VectorType[], MatrixType[], int i) const;
  std::string variables() const {
    return m_fun[0].variables();
  }

  virtual void setParameter(const std::string &name, const ScalarType& value);
  virtual void setOrder(int the_new);
  int dimension() const{
    return m_dim;
  }

  void differentiateTime() const;
  void setCurrentTime(const ScalarType& a_time) const;
  const ScalarType& getCurrentTime() const
  {
    return m_fun[0].getCurrentTime(m_dim);
  }

protected:
  int m_dim, m_order;
  FunctionType *m_fun;
  FunctionType *m_der; // partial derivatives of a map, in fact dim*dim functions

private:
  void createFromText(const std::string &,int);
  void createFromObject(const Map &);
}; // the end of class Map


/*________________________________________________*/

template<typename MatrixType>
inline const typename Map<MatrixType>::FunctionType& Map<MatrixType>::operator()(int i) const
{
  return m_fun[i-1];
}

template<typename MatrixType>
inline  typename Map<MatrixType>::VectorType Map<MatrixType>::operator()(const VectorType &x, MatrixType &dF) const
{
  dF = operator[](x);
  return operator()(x);
}


}} // the end of the namespace capd::map

#endif // _CAPD_MAP_MAP_H_ 

/// @}
