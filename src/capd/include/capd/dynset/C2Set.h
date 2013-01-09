/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2Set.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_C2SET_H_ 
#define _CAPD_DYNSET_C2SET_H_ 

#include <string>

#include "capd/dynsys/C2DynSys.h"
#include "capd/vectalg/Norm.h"
#include "capd/map/C2Coeff.h"

namespace capd{
namespace dynset{

template<typename MatrixT>
class C2Set{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::map::C2Coeff<ScalarType> C2CoeffType;
  typedef C2Set SetType;
  typedef capd::dynsys::C2DynSys<MatrixType> DynSysType;

 /* virtual C2Set *clone(void) const = 0;
  virtual C2Set *fresh(void) const = 0;
  virtual C2Set *cover(const VectorType &v) const = 0;
  virtual ScalarType size(void) const = 0;
  virtual VectorType center(void) const = 0;*/
  virtual void move(capd::dynsys::C2DynSys<MatrixType> &c2dynsys) = 0;
  virtual const NormType *getNorm(void) const = 0;

  virtual std::string show(void) const;
  virtual operator VectorType() const = 0;
  virtual operator MatrixType() const = 0;
  virtual const ScalarType& operator()(int i, int j, int c) const = 0;
  virtual VectorType operator()(int j, int c) const = 0;
  virtual MatrixType operator()(int i) = 0;
  virtual ~C2Set(){}
};


template<typename MatrixType>
inline std::string C2Set<MatrixType>::show(void) const
{
  return "This is an unkonown set";
}

}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_C2SET_H_ 

/// @}
