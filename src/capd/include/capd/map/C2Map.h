/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2Map.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak  2000-2005 */

#ifndef _CAPD_MAP_C2MAP_H_ 
#define _CAPD_MAP_C2MAP_H_ 

#include <string>
#include <stdexcept>
#include <sstream>
#include <vector>
#include <new>
#include "capd/map/Map.h"
#include "capd/map/C2Coeff.h"

namespace capd{
namespace map{

// ----------------------------------------------

template<typename MatrixT>
class C2Map : public Map<MatrixT>
{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename VectorType::ScalarType ScalarType;
  typedef Function<VectorType> FunctionType;
  typedef C2Coeff<ScalarType> C2CoeffType;

  C2Map(void);
  C2Map(const std::string &, int order=0);
  C2Map(const char *, int order=0);
  C2Map(const C2Map &);
  virtual ~C2Map(){
    delete []m_c2der;
  }

  C2Map& operator=(const char *);
  C2Map& operator=(const std::string &);
  C2Map& operator=(const C2Map &);

  void setOrder(int);
  void setParameter(const std::string &name, const ScalarType& value);
  C2CoeffType* computeSecondDerivatives(VectorType [], int) const;
  void computeSecondDerivatives(const VectorType &iv, C2CoeffType &result) const;

  void differentiateTime() const;
  void setCurrentTime(const ScalarType& a_time) const;
  
  using Map<MatrixType>::variational;
  using Map<MatrixType>::variables;
  using Map<MatrixType>::dimension;
  using Map<MatrixType>::getCurrentTime;

protected:
  using Map<MatrixType>::m_dim;
  using Map<MatrixType>::m_fun;
  using Map<MatrixType>::m_der;
  using Map<MatrixType>::m_order;

  FunctionType* m_c2der; // a table of second partial derivaties, c2der = new FunctionType[dim*dim*(dim+1)/2]

private:
  void allocateC2Der();
}; // the end of class Map


}} // the end of the namespace capd::map

#endif // _CAPD_MAP_C2MAP_H_ 

/// @}
