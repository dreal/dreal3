/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicCnTaylor.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_BASICCNTAYLOR_HPP_
#define _CAPD_DYNSYS_BASICCNTAYLOR_HPP_

#include "capd/capd/power.h"
#include "capd/dynsys/BasicCnTaylor.h"
#include "capd/map/CnContainer.h"
#include "capd/map/Node.hpp"

namespace capd{
namespace dynsys{

template<typename CnMapT, typename StepControlType>
BasicCnTaylor<CnMapT,StepControlType>::~BasicCnTaylor(){}

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::setOrder(int a_order)
{
  if(m_order==a_order+1)
    return;
  m_order = a_order+1;
  m_vectorField->setOrder(m_order);
  m_vectorFieldSeries.setOrder(a_order+2);
  m_resultSeries.setOrder(a_order+2);
  m_compositionFormula.setOrder(a_order+2);
}

// ---------------------------- CONSTRUCTORS ---------------------------------------------

template<typename CnMapT, typename StepControlType>
BasicCnTaylor<CnMapT,StepControlType>::BasicCnTaylor(
      CnMapType& a_vectorField,
      int a_order,
      const ScalarType& a_step,
      const StepControlType& stepControl
    )
  : capd::dynsys::StepControlInterface<StepControlType>(stepControl),
    m_vectorField(&a_vectorField), m_step(a_step), m_order(a_order+1),
    m_vectorFieldSeries(a_vectorField.dimension(),a_vectorField.getRank(),a_order+2),
    m_resultSeries(a_vectorField.dimension(),a_vectorField.getRank(),a_order+2),
    m_compositionFormula(a_vectorField.dimension(),a_vectorField.getRank(),true),
    m_nonlinearPart(a_vectorField.dimension(),a_vectorField.getRank(),true),
    m_zeroNode(a_order+3,ScalarType(0))
{
  if(m_vectorField->getOrder()!=m_order)
    m_vectorField->setOrder(m_order);

  Multiindex::generateList(dimension(),getRank(),m_listIndices);
  computeCompositionFormula();
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
typename BasicCnTaylor<CnMapT,StepControlType>::NodeType&
BasicCnTaylor<CnMapT,StepControlType>::computeProduct(const Multiindex& mi, const Multipointer& a, int p, int k)
{
  NodeType* result=0;
  bool first = true;
  const typename Multipointer::IndicesSet& is = Multipointer::generateList(p,k);
  typename Multipointer::IndicesSet::const_iterator b=is.begin(), e=is.end();
  while(b!=e)
  {
    typename Multipointer::MultipointersVector::const_iterator bt = b->begin(), et=b->end();
    typename Multiindex::const_iterator ib= mi.begin();

    Multipointer delta = a.subMultipointer(*bt);
    NodeType* temp = m_resultSeries(*ib,delta);
    ++bt;
    ++ib;
    while(bt!=et)
    {
      Multipointer delta = a.subMultipointer(*bt);
      temp = &( (*temp) * (*m_resultSeries(*ib,delta)) );
      ++bt;
      ++ib;
    }

    ++b;

    if(first)
    {
      result = temp;
      first = false;
    }else
      result = &( (*temp) + (*result) );
  }
  return *result;
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::computeCompositionFormula(const Multipointer& a)
{
  int p = a.module(),i;
  capd::map::CnContainer<bool> mask(dimension(),getRank());
  m_vectorField->getMask(mask);

  for(int k=2;k<=p;++k)
  {
    typename Multiindex::MultiindexVector::iterator b = m_listIndices[k-1].begin(), e=m_listIndices[k-1].end();
    while(b!=e)
    {
      Multipointer mp(b->dimension(),b->begin());
      std::sort(mp.begin(),mp.end());
      NodeType * product = 0;
      for(i=0;i<dimension();++i)
      {
        if(!(product || mask(i,mp)) )
          product = &(computeProduct(*b,a,p,k));

        if(mask(i,mp))
          continue;

        NodeType& temp = *(m_vectorFieldSeries(i,mp)) * (*product);
        if(m_nonlinearPart(i,a))
          m_nonlinearPart(i,a) = &( *(m_nonlinearPart(i,a)) + temp);
        else
          m_nonlinearPart(i,a) = &temp;
      }
      ++b;
    }
  }

  if(p>=2)
    for(i=0;i<dimension();++i)
      if(!(m_nonlinearPart(i,a)))
      {
        m_nonlinearPart(i,a) = &m_zeroNode;
        m_zeroNode.m_links++;
      }
// for k=1
  typename Multiindex::MultiindexVector::iterator b = m_listIndices[0].begin(), e=m_listIndices[0].end();
  while(b!=e)
  {
    Multipointer mp(b->dimension(),b->begin());
    std::sort(mp.begin(),mp.end());
    NodeType* product = 0;

    for(i=0;i<dimension();++i)
    {
      if(!(product || mask(i,mp)) )
        product = &(computeProduct(*b,a,p,1));

      if(mask(i,mp))
        continue;

      NodeType& temp = *(m_vectorFieldSeries(i,mp)) * (*product);
      if(m_compositionFormula(i,a))
        m_compositionFormula(i,a) = &( *(m_compositionFormula(i,a)) + temp );
      else if(m_nonlinearPart(i,a))
      {
        m_compositionFormula(i,a) = &( *(m_nonlinearPart(i,a)) + temp );
        (m_nonlinearPart(i,a)->m_links)++;
      }
      else
        m_compositionFormula(i,a) = &temp;
    }

    ++b;
  }

  for(i=0;i<dimension();++i)
    if(!(m_compositionFormula(i,a)))
      {
        m_compositionFormula(i,a) = &m_zeroNode;
        m_zeroNode.m_links++;
      }

  for(i=0;i<dimension();++i)
    (m_compositionFormula(i,a)->m_links)++;
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::computeCompositionFormula()
{
// for rank==0
  for(int j=0;j<dimension();++j)
  {
    m_compositionFormula(j) = m_vectorFieldSeries(j);
    (m_compositionFormula(j)->m_links)++;
  }

  for(int i=1;i<=getRank();++i)
  {
    Multipointer a = m_compositionFormula.first(i);
    do{
      computeCompositionFormula(a);
    }while(m_compositionFormula.next(a));
  }
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
typename BasicCnTaylor<CnMapT,StepControlType>::VectorType
BasicCnTaylor<CnMapT,StepControlType>::operator()(CnCoeffType& coeff)
{
  if(dimension()!=coeff.dimension())
    throw std::runtime_error("BasicCnTaylor::operator(CnCoeffType&) - incompatible dimensions");
  int rank = coeff.rank();
  if( getRank() < rank )
    throw std::runtime_error("BasicCnTaylor::operator(CnCoeffType&) - requested rank to large");

  setInitialCondition(coeff);
  computeVectorFieldSeries(VectorType(coeff),rank,m_order);
  computeResultSeries(rank,m_order);

  coeff.clear();
  for(int j=m_order-1;j>=0;--j)
  {
    for(int i=0;i<dimension();++i)
    {
      typename SeriesContainerType::const_iterator it=m_resultSeries.begin(i);
      typename CnCoeffType::iterator b = coeff.begin(i), e=coeff.end(i,rank);
      while(b!=e)
      {
        (*b) = (*b) * m_step + (*it)->value[j];
        ++b;
        ++it;
      }
    }
  }

  return VectorType(coeff);
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::setInitialCondition(const CnCoeffType& coeff)
{
  for(int i=0;i<dimension();++i)
  {
    typename CnCoeffType::const_iterator b=coeff.begin(i), e=coeff.end(i,coeff.rank());
    typename SeriesContainerType::const_iterator j=m_resultSeries.begin(i), p = m_compositionFormula.begin(i);
    while(b!=e)
    {
      (*j)->value[0] = *b;
      (*p)->reset();
      ++b;
      ++j;
      ++p;
    }
  }
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::setInitialCondition(const VectorType& v, const MatrixType& m)
{
  int i,j;
  for(i=0;i<dimension();++i)
  {
    m_resultSeries(i)->value[0] = v[i];
    for(j=0;j<dimension();++j)
      m_resultSeries(i,j)->value[0] = m(i+1,j+1);
  }
  typename SeriesContainerType::const_iterator b,e;
  for(j=2;j<=getRank();++j)
    for(i=0;i<dimension();++i)
    {
      b=m_resultSeries.begin(i,j);
      e=m_resultSeries.end(i,j);
      while(b!=e)
      {
        (*b)->value[0]=ScalarType(0);
        ++b;
      }
    }

  b=m_compositionFormula.begin();
  e=m_compositionFormula.end();
  while(b!=e)
  {
    (*b)->reset();
    ++b;
  }
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::setInitialCondition(const VectorType& v, const MatrixType& m, const C2CoeffType& hessian)
{
  int i,j,c;
  for(i=0;i<dimension();++i)
  {
    m_resultSeries(i)->value[0] = v[i];
    for(j=0;j<dimension();++j)
    {
      m_resultSeries(i,j)->value[0] = m(i+1,j+1);
      for(c=j;c<dimension();++c)
        m_resultSeries(i,j,c)->value[0] = hessian(i,j,c);
    }
  }
  typename SeriesContainerType::const_iterator b,e;
  for(j=3;j<=getRank();++j)
    for(i=0;i<dimension();++i)
    {
      b=m_resultSeries.begin(i,j);
      e=m_resultSeries.end(i,j);
      while(b!=e)
      {
        (*b)->value[0]=ScalarType(0);
        ++b;
      }
    }

  b=m_compositionFormula.begin();
  e=m_compositionFormula.end();
  while(b!=e)
  {
    (*b)->reset();
    ++b;
  }
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::setInitialCondition(const VectorType& v)
{
  for(int i=0;i<dimension();++i)
    m_resultSeries(i)->value[0] = v[i];

  typename SeriesContainerType::const_iterator b=m_compositionFormula.begin(), e=m_compositionFormula.end();
  while(b!=e)
  {
    (*b)->reset();
    ++b;
  }
}


// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::computeVectorFieldSeries(const VectorType& v, int rank, int a_order)
{
  VectorType x = v;
  for(int j=0;j<a_order;++j)
  {
    m_vectorField->computeDerivatives(x,m_vectorFieldSeries,j,0,rank);
    for(int i=0;i<dimension();++i)
      x[i] = m_resultSeries(i)->value[j+1] = m_vectorFieldSeries(i)->value[j]/(j+1);
  }
}


// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::computeResultSeries(int rank, int a_order)
{
  for(int p=0;p<a_order;++p)
    for(int r=1;r<=rank;++r)
    {
      for(int i=0;i<dimension();++i)
      {
        typename SeriesContainerType::const_iterator
               b = m_compositionFormula.begin(i,r),
               e = m_compositionFormula.end(i,r),
               j = m_resultSeries.begin(i,r);
        while(b!=e)
        {
          (*j)->value[p+1] = (*b)->operator()(p)/(p+1);
          ++b;
          ++j;
        }
      }
    }
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::computeNonlinearPart(int rank)
{
  for(int i=0;i<dimension();++i)
  {
    typename SeriesContainerType::const_iterator
         b = m_nonlinearPart.begin(i,rank),
         e = m_nonlinearPart.end(i,rank);
    while(b!=e)
    {
      (*b)->operator()(0);
      ++b;
    }
  }
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
typename BasicCnTaylor<CnMapT,StepControlType>::VectorType
BasicCnTaylor<CnMapT,StepControlType>::operator()(const VectorType& iv)
{
  computeVectorFieldSeries(iv,0,m_order);
  setInitialCondition(iv);
  VectorType result(dimension());
  int i,j;
  for(i=0;i<dimension();++i)
    result[i] = m_resultSeries(i)->value[m_order];

  for(j=m_order-1;j>=0;--j)
  {
    for(i=0;i<dimension();++i)
      result[i] = result[i]*m_step + m_resultSeries(i)->value[j];
  }
  return result;
}

// ---------------------------------------------------------------------------------------

template <typename MapType, typename StepControlType>
typename BasicCnTaylor<MapType, StepControlType>::VectorType BasicCnTaylor<MapType, StepControlType>::operator()(const VectorType &iv, MatrixType& der)
{
   return (*this)(iv, MatrixType::Identity(dimension()), der);
}

template<typename CnMapT, typename StepControlType>
typename BasicCnTaylor<CnMapT,StepControlType>::VectorType
BasicCnTaylor<CnMapT,StepControlType>::operator()(const VectorType &iv, const MatrixType& derivative, MatrixType& result)
{
  setInitialCondition(iv, derivative);
  computeVectorFieldSeries(iv,1,m_order);
  computeResultSeries(1,m_order);
  VectorType x(dimension());

  int i,j,c;
  for(i=0;i<dimension();++i)
  {
    x[i] = m_resultSeries(i)->value[m_order];
    for(j=0;j<dimension();++j)
      result(i+1,j+1) = m_resultSeries(i,j)->value[m_order];
  }
  for(c=m_order-1;c>=0;--c)
    for(i=0;i<dimension();++i)
    {
      x[i] = x[i]*m_step + m_resultSeries(i)->value[c];
      for(j=0;j<dimension();++j)
        result(i+1,j+1) = result(i+1,j+1)*m_step + m_resultSeries(i,j)->value[c];
    }
  return x;
}


template <typename MapType, typename StepControlType>
typename BasicCnTaylor<MapType, StepControlType>::VectorType BasicCnTaylor<MapType, StepControlType>::operator()(capd::map::C1Coeff<MatrixType> & coeffs)
{
  coeffs = (*this)((VectorType)coeffs, coeffs.getDerivative(), coeffs.refDerivative());
  return (VectorType)coeffs;
}


// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
const typename BasicCnTaylor<CnMapT,StepControlType>::SeriesContainerType&
   BasicCnTaylor<CnMapT,StepControlType>::computeDaPhi(const CnCoeffType& c, int order)
{
  if(order>m_order+1)
    throw std::runtime_error("BasicCnTaylor::computeComposition - requested order to large");
  setInitialCondition(c);
  computeVectorFieldSeries(VectorType(c),c.rank(),order);
  computeResultSeries(c.rank(),order);
  return m_resultSeries;
}


// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
typename BasicCnTaylor<CnMapT,StepControlType>::ScalarType
BasicCnTaylor<CnMapT,StepControlType>::getCoeffNorm(int order) const
{
  if(order>m_order+1)
    throw std::runtime_error("BasicCnTaylor::getCoeffNorm - requested order to large");

  ScalarType result(0);
  for(int i=0;i<dimension();++i)
    result += power(m_resultSeries(i)->value[order],2);
  return sqrt(result);
}

// ---------------------------------------------------------------------------------------

template<typename CnMapT, typename StepControlType>
void BasicCnTaylor<CnMapT,StepControlType>::clearCoefficients()
{
  ScalarType zero(0);
  for(int i=0;i<dimension();++i)
  for(int r=0;r<=this->getOrder()+1;++r)
    m_resultSeries(i)->value[r] = zero;
}

}} // the end of the namespace capd::dynsys

#endif // _CAPD_DYNSYS_BASICCNTAYLOR_HPP_

/// @}
