/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file  PoincareMap.hpp
///
/// @author Daniel Wilczak
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_POINCARE_POINCARE_MAP_HPP_
#define _CAPD_POINCARE_POINCARE_MAP_HPP_

#include <cassert>
#include "capd/poincare/PoincareMap.h"
#include "capd/poincare/BasicPoincareMap.hpp"

namespace capd{
namespace poincare{

template <typename DS, typename FunT>
typename PoincareMap<DS,FunT>::BoundType PoincareMap<DS,FunT>::timeStepCorrectionFactor = 0.9;

template <typename DS, typename FunT>
int PoincareMap<DS,FunT>::maxCorrectionTries = 10;

template <typename DS, typename FunT>
typename PoincareMap<DS,FunT>::ScalarType
PoincareMap<DS,FunT>::minCrossingTimeStep
  = typename PoincareMap<DS,FunT>::ScalarType(1.0e-15);

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
void PoincareMap<DS,FunT>::computeJacEnclosure(C1Set& S, VectorType& V)
{
  if(derivativeOfFlow!=NULL)
  {
    MatrixType enc = this->m_dynamicalSystem.jacEnclosure(V,*(S.getNorm()));
    MatrixType oneStepBound = enc*MatrixType(S);
    for(int i=0;i<this->m_dim;i++)
      for(int j=0;j<this->m_dim;j++)
        (*derivativeOfFlow)[i][j] = intervalHull((*derivativeOfFlow)[i][j],oneStepBound[i][j]);
  }
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
void PoincareMap<DS,FunT>::computeJacEnclosure(C2Set& S, VectorType& enc)
{
  if(this->derivativeOfFlow!=NULL)
  {
    int i,j,c;
    MatrixType jacEnc = this->m_dynamicalSystem.jacEnclosure(enc,*(S.getNorm()));
    MatrixType currentDerivative = MatrixType(S);

// computation of the hessian of Poincare map

    if(hessianOfFlow!=NULL)
    {
      MatrixType* oneStepHessian = new (this->m_dim,this->m_dim) MatrixType[this->m_dim];
      typename C2Set::C2CoeffType EH(this->m_dim); // EH will be an enclosure for the hessian part
      this->m_dynamicalSystem.c2Enclosure(enc,jacEnc,*(S.getNorm()),EH);
      int ss,r;

      for(i=0;i<this->m_dim;++i)
        oneStepHessian[i].clear();

      for(i=0;i<this->m_dim;++i)
        for(j=0;j<this->m_dim;++j)
          for(c=0;c<this->m_dim;++c)
            for(ss=0;ss<this->m_dim;++ss)
              for(r=0;r<this->m_dim;++r)
                //oneStepHessian[i][j][c] += EH(i,ss,r) * (*derivativeOfFlow)[ss][j] * (*derivativeOfFlow)[r][c];
                  oneStepHessian[i][j][c] += EH(i,ss,r) * currentDerivative[ss][j] * currentDerivative[r][c];

      for(i=0;i<this->m_dim;++i)
        for(j=0;j<this->m_dim;++j)
          for(c=0;c<this->m_dim;++c)
            for(ss=0;ss<this->m_dim;++ss)
              oneStepHessian[i][j][c] += jacEnc[i][ss] * S(ss,j,c)/*hessianOfFlow[ss][j][c]*/;

      for(i=0;i<this->m_dim;i++)
        for(j=0;j<this->m_dim;j++)
          for(c=0;c<this->m_dim;c++)
            this->hessianOfFlow[i][j][c] = intervalHull(this->hessianOfFlow[i][j][c],oneStepHessian[i][j][c]);

      delete []oneStepHessian;
    } // end if(hessianOfFlow!=NULL)

// computation of enclosure for derivative of the Poincare map
    MatrixType oneStepBound = jacEnc*currentDerivative;
    for(i=0;i<this->m_dim;i++)
      for(j=0;j<this->m_dim;j++)
        (*derivativeOfFlow)[i][j] = intervalHull((*derivativeOfFlow)[i][j],oneStepBound[i][j]);
  } // end of if(derivativeOfFlow!=NULL)
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
void PoincareMap<DS,FunT>::computeJacEnclosure(CnSet& S, VectorType& )
{
  if(partialDerivatives!=NULL)
  {
    CnCoeffType enc(this->m_dim,partialDerivatives->rank()),
                    oneStepBound(this->m_dim,partialDerivatives->rank()
                   );

    this->m_dynamicalSystem.cnEnclosure(VectorType(S),enc,*(S.getNorm()));
    substitutionPowerSeries(enc,S.currentSet(),oneStepBound,false);

    for(int p=0;p<this->m_dim;++p)
    {
      typename CnCoeffType::iterator b=partialDerivatives->begin(p,1),
                                     e=partialDerivatives->end(p,partialDerivatives->rank());
      typename CnCoeffType::iterator i=oneStepBound.begin(p,1);
      while(b!=e)
      {
        *b = intervalHull(*b,*i);
        ++b;
        ++i;
      }
    }
  }
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
void PoincareMap<DS,FunT>::saveMatrices(CnSet& S)
{
  if(partialDerivatives!=NULL)
    *partialDerivatives = S.currentSet();
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
void PoincareMap<DS,FunT>::saveMatrices(C2Set& S)
{
  if(derivativeOfFlow!=NULL)
    *derivativeOfFlow = MatrixType(S);

  if(hessianOfFlow!=NULL)
  {
    int i,j,c;
    for(i=0;i<this->m_dim;++i)
      for(j=0;j<this->m_dim;++j)
        for(c=0;c<this->m_dim;++c)
          hessianOfFlow[i][j][c] = S(i,j,c);
  }
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
void PoincareMap<DS,FunT>::saveMatrices(C1Set& S)
{
  if(derivativeOfFlow!=NULL)
    *derivativeOfFlow = MatrixType(S);
}

}} // namespace capd::poincare

#endif // _CAPD_POINCARE_POINCARE_MAP_HPP_

/// @}
