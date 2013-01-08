/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C0Set.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0SET_H_
#define _CAPD_DYNSET_C0SET_H_

#include <string>
#include <sstream>
#include "capd/dynsys/DynSys.h"

namespace capd{
/**
 * Various set representations that can be moved with dynamical systems
 */
namespace dynset{

/**
 * Common interface of all sets that stores only C0 information (set position).
 */
template<typename MatrixT>
class C0Set{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef C0Set SetType;                                   ///<  defines class of given set (C0, C1, C2, ...)
  typedef capd::dynsys::DynSys<MatrixType> DynSysType;     ///< defines minimal regularity of the dynamical system

   /// destructor
  virtual ~C0Set (void) {}
    /// computes image of the set after one step/iterate of the dynamical system
  virtual void move(DynSysType & dynsys) = 0;
    /// returns a set in the canonical frame
  virtual operator VectorType() const = 0;
    /// returns a set detailed information
  virtual std::string show() const = 0;
  
};

}} //namespace capd::dynset

#endif // _CAPD_DYNSET_C0SET_H_

/// @}
