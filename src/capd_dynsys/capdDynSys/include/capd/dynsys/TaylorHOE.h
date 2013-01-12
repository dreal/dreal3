/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file TaylorHOE.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

/* Author: Daniel Wilczak 2010 */

#ifndef _CAPD_DYNSYS_TAYLORHOE_H_
#define _CAPD_DYNSYS_TAYLORHOE_H_

#include <string>
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/Taylor.h"

namespace capd{
namespace dynsys{

template<typename MapT, typename StepControlT = capd::dynsys::ILastTermsStepControl>
class TaylorHOE: public Taylor<MapT,StepControlT>
{
public:
  typedef MapT MapType;
  typedef StepControlT StepControlType;
  typedef typename MapT::FunctionType FunctionType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  TaylorHOE(MapType& vField, int order, const ScalarType& step, const StepControlT& stepControl = StepControlT());

  /// it computes image of the set (in give representation) using set.move function
  template <typename SetType>
  void operator()(SetType & set){
    set.move(*this);
  }

  virtual void encloseMap(
      const VectorType& x,
      const VectorType& xx,
      VectorType& o_phi,
      MatrixType& o_jacPhi,
      VectorType& o_rem
  );

  virtual void encloseMap(
      const VectorType& x,
      const VectorType& xx,
      VectorType& o_phi,
      MatrixType& o_jacPhi,
      VectorType& o_rem,
      MatrixType& o_jacRem,
      const NormType& norm
  );
  using Taylor<MapT,StepControlT>::operator ();

  VectorType Remainder(const VectorType& x) ;
  VectorType enclosure(const VectorType& x, int* found) ;
  VectorType enclosure(const VectorType &x) ;
  VectorType enclosure(const VectorType &x, VectorType& out_remainder, int* found, bool computeCoeff=true) ;

protected:
  void operator=(const TaylorHOE& ){}
  TaylorHOE(const TaylorHOE& t) : BasicTaylor<MapT,StepControlT>(t), Taylor<MapT,StepControlT>(t){}
};

//###########################################################//

template<typename MapType, typename StepControlType>
inline
typename TaylorHOE<MapType,StepControlType>::VectorType
TaylorHOE<MapType,StepControlType>::enclosure(const VectorType &x, int *found)
///<the function finds an enclosure for \varphi([0,step],x)
{
  bool stepChangeAllowance = this->isStepChangeAllowed();
  this->turnOffStepControl();
  VectorType remainder(x.dimension());
  VectorType result = this->enclosure(x,remainder,found);
  this->setStepChangeAllowance(stepChangeAllowance);
  return result;
}

//###########################################################//

template<typename MapType, typename StepControlType>
inline
typename TaylorHOE<MapType,StepControlType>::VectorType
TaylorHOE<MapType,StepControlType>::enclosure(const VectorType &x)
///<the function finds an enclosure for \varphi([0,step],x)
{
  bool stepChangeAllowance = this->isStepChangeAllowed();
  this->turnOffStepControl();
  VectorType remainder(x.dimension());
  VectorType result = this->enclosure(x,remainder,NULL);
  this->setStepChangeAllowance(stepChangeAllowance);
  return result;
}

//###########################################################//

template<typename MapType, typename StepControlType>
inline
typename TaylorHOE<MapType,StepControlType>::VectorType
TaylorHOE<MapType,StepControlType>::Remainder(const VectorType &x)
///<the function finds an enclosure for \varphi([0,step],x)
{
  bool stepChangeAllowance = this->isStepChangeAllowed();
  this->turnOffStepControl();
  VectorType remainder(x.dimension());
  this->enclosure(x,remainder,NULL);
  this->setStepChangeAllowance(stepChangeAllowance);
  return remainder;
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_TAYLORHOE_H_

/// @}
