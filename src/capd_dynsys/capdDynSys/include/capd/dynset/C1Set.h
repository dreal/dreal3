////////////////////////////////////////////////////////////////////////////
/// @file C1Set.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C1SET_H_
#define _CAPD_DYNSET_C1SET_H_

#include <string>

#include "capd/dynsys/C1DynSys.h"
#include "capd/vectalg/Norm.h"

namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

/**
 * Common interface of all sets that store C1 informations (set position and first derivatives)
 */
template<typename MatrixT>
class C1Set{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef C1Set SetType;                                     ///< defines class of given set (C0, C1, C2, ...)
  typedef capd::dynsys::C1DynSys<MatrixType> DynSysType;     ///< defines minimal regularity of the dynamical system

/*
   /// returns a copy of the set
  virtual SetType * clone(void) const = 0;
   /// returns a 'fresh' instance of the set
  virtual SetType * fresh(void) const = 0;
   /// returns a set that covers given interval vector
  virtual SetType * cover(const VectorType &v) const = 0;
  */
   /// destructor
  virtual ~C1Set(){}

   /// computes image of the set after one step/iterate of the dynamical system
  virtual void move(DynSysType & c1dynsys) = 0;

   /// returns an eclosure of the set in the canonical coordinates
  virtual operator VectorType() const = 0;
   /// returns derivative
  virtual operator MatrixType() const = 0;

   /// returns used norm
  virtual const NormType* getNorm(void) const = 0;

   /// returns a set detailed information
  virtual std::string show(void) const = 0;
/*
  virtual ScalarType size(void) const = 0;
  virtual VectorType center(void) const = 0;
*/
};

/// @}
}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_C1SET_H_

