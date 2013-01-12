/////////////////////////////////////////////////////////////////////////////
/// @file CnSet.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

/* Author: Daniel Wilczak 2006 */

#ifndef _CAPD_DYNSET_CNSET_H_ 
#define _CAPD_DYNSET_CNSET_H_ 

#include "capd/dynsys/CnDynSys.h"
#include "capd/vectalg/Norm.h"
#include "capd/vectalg/Multiindex.h"

namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

/**
 * Common interface of all sets that store Cn information (set position and derivatives to order n)
 */
template<typename MatrixT>
class CnSet{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename MatrixType::RefColumnVectorType RefVectorType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::vectalg::Multipointer Multipointer;
  typedef capd::vectalg::Multiindex Multiindex;
  typedef capd::map::CnCoeff<MatrixType> CnCoeffType;
  typedef CnSet SetType;
  typedef capd::dynsys::CnDynSys<MatrixType> DynSysType;

  /*virtual CnSet* clone(void) const = 0;
  virtual ScalarType size(void) const = 0;
  virtual VectorType center(void) const = 0;*/
  virtual void move(DynSysType & cndynsys) = 0;
  virtual const NormType* getNorm(void) const = 0;
  virtual int getRank() const = 0;
  virtual int getDimension() const = 0;
  virtual const CnCoeffType& currentSet() const = 0;
  virtual CnCoeffType& currentSet() = 0;
   
  virtual operator VectorType() const = 0;
  virtual operator MatrixType() const = 0;
  // this operators returns d^{mp}f_i
  virtual const ScalarType& operator()(int i,const Multiindex& mp) const = 0;
  // this operator returns a vector of partial derivatives, i.e. result[i] = d^{mp}f_i
  virtual RefVectorType operator()(const Multipointer& mp) const = 0;
  // indexing for C^2
  virtual const ScalarType& operator()(int i, int j, int c) const = 0;

  // indexing for C^1   
  virtual const ScalarType& operator()(int j, int c) const = 0;
  // indexing for C^0
  virtual const ScalarType& operator()(int i) const = 0;
  virtual ~CnSet(){}
};

/// @}
}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_CNSET_H_ 
