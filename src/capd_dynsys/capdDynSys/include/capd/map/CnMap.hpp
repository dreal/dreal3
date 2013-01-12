/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnMap.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2006 */

#ifndef _CAPD_MAP_CNMAP_HPP_
#define _CAPD_MAP_CNMAP_HPP_

#include <string>
#include <sstream>
#include <stdexcept>
#include <vector>

#include "capd/map/CnCoeff.hpp"
#include "capd/map/C2Coeff.hpp"
#include "capd/map/BasicFunction.hpp"
#include "capd/map/CnMap.h"
#include "capd/map/Parser.h"

namespace capd{
namespace map{

/*___________________________________________*/

template<typename MatrixT, int rank>
void CnMap<MatrixT,rank>::reset() const
{
  typename TreesContainer::const_iterator b=m_trees.begin(), e=m_trees.end();
  while(b!=e)
  {
    (*b)->reset();
    ++b;
  }
}

/*___________________________________________*/

template<typename MatrixT, int rank>
void CnMap<MatrixT,rank>::setArgument(const VectorType& v, int j) const
{
  if(!j) reset();
  for(int i=0;i<dimension();++i)
    m_val[m_order*i+j] = v[i];
}

/*___________________________________________*/

template<typename MatrixT, int rank>
void CnMap<MatrixT,rank>::computeSecondDerivatives(const VectorType& iv, C2CoeffType& result) const
{
  int dim=dimension();
  setArgument(iv);
  int i,j,c;
  for(i=0;i<dim;++i)
    for(j=0;j<dim;++j)
      for(c=j;c<dim;++c)
          result(i,j,c) = m_trees(i,j,c)->operator()(0);
}

/*___________________________________________*/

template<typename MatrixT, int rank>
typename CnMap<MatrixT,rank>::C2CoeffType* CnMap<MatrixT,rank>::computeSecondDerivatives(VectorType iv[], int p) const
{
  int dim=dimension();
  C2CoeffType* result = new (dim) C2CoeffType[p+1];
  int i,j,c,r;

  for(r=0;r<=p;++r)
  {
    setArgument(iv[r],r);
    for(i=0;i<dim;++i)
      for(j=0;j<dim;++j)
        for(c=j;c<dim;++c)
            result[r](i,j,c) = m_trees(i,j,c)->operator()(r);
  }
  return result;
}


/*___________________________________________*/

template<typename MatrixT, int rank>
void CnMap<MatrixT,rank>::variational(VectorType iv[], MatrixType im[], int p) const
{
  if(p<0)
  {
    throw std::out_of_range ("exception in void CnMap::variational(VectorType iv[], MatrixType im[], int p)\nnegative index of Taylor coefficient");
  }

  if(p>m_order)
  {
    std::ostringstream s;
    s << "exception in void CnMap::variational(VectorType iv[], MatrixType im[], int p)\n";
    s << "Cannot compute " << p << "-th Taylor coefficient\n";
    s << "The order is " << m_order;
    throw std::out_of_range (s.str());
  }
  int dim=dimension();
  for(int r=0;r<=p;++r)
  {
    setArgument(iv[r],r);
    for(int i=0;i<dim;++i)
      for(int j=0;j<dim;++j)
        im[r][i][j] = m_trees(i,j)->operator()(r);
  }
}


/*___________________________________________*/

template<typename MatrixT, int rank>
void CnMap<MatrixT,rank>::computeDerivatives(const VectorType& v, CnCoeffType& result, int r) const
{
  if(r>m_order){
    std::ostringstream message;
    message << "CnMap::computeDerivatives - requested order=" << r << " is to large!\n";
    message << "Object CnMap has order=" << m_order << "\n";
    throw std::runtime_error(message.str());
  }
  if( (result.dimension()!=dimension()) ){
    throw std::runtime_error("CnMap::computeDerivatives - Incompatible dimensions of CnCoeff and CnMap");
  }
  if(  result.rank()>getRank() ){
     throw std::runtime_error("CnMap::computeDerivatives - Rank is too big");
  }

  setArgument(v,r);
  for(int j=0;j<dimension();++j)
  {
    typename TreesContainer::const_iterator b=m_trees.begin(j), e=m_trees.end(j,result.rank());
    typename CnCoeffType::iterator i=result.begin(j);
    while(b!=e)
    {
      *i = (*b)->operator()(r);
      ++b;
      ++i;
    }
  }
}

/*___________________________________________*/

template<typename MatrixT, int rank>
void CnMap<MatrixT,rank>::computeDerivatives(const VectorType& v, const SeriesContainerType& result, int a_order, int a_minRank, int a_maxRank) const
{
  if(a_order>m_order)
  {
    std::ostringstream message;
    message << "CnMap::computeDerivatives - requested order=" << a_order << " is to large!\n";
    message << "Object CnMap has order=" << m_order << "\n";
    throw std::runtime_error(message.str());
  }
  if( (result.dimension()!=dimension()) || (a_maxRank > getRank()) || (a_maxRank > result.rank()) || (a_minRank<0) || (a_minRank>a_maxRank) )
  {
    throw std::runtime_error("CnMap::computeDerivatives - Incompatible dimension or order of SeriesContainer and CnMap");
  }
  setArgument(v,a_order);
  for(int j=0;j<dimension();++j)
  {
    typename TreesContainer::const_iterator b=m_trees.begin(j,a_minRank), e=m_trees.end(j,a_maxRank);
    typename SeriesContainerType::const_iterator i=result.begin(j,a_minRank);
    while(b!=e)
    {
      (*i)->value[a_order] = (*b)->operator()(a_order);
      ++b;
      ++i;
    }
  }
}

/*___________________________________________*/

template<typename MatrixT, int rank>
MatrixT CnMap<MatrixT,rank>::operator[](const VectorType& v) const
{
  setArgument(v);
  int dim=dimension(), i=0;
  MatrixType m(dim,dim);

  typename MatrixType::iterator mb=m.begin(), me=m.end();
  while(mb!=me)
  {
    typename TreesContainer::const_iterator b1=m_trees.begin(i,1), e1=m_trees.end(i,1);
    while(b1!=e1)
    {
      *mb = (*b1)->operator()(0);
      ++mb;
      ++b1;
    }
    ++i;
  }
  return m;
}

/*___________________________________________*/

template<typename MatrixT, int rank>
typename CnMap<MatrixT,rank>::VectorType
  CnMap<MatrixT,rank>::operator()(const VectorType& v, MatrixType& m) const
{
  setArgument(v);
  VectorType result(dimension());
  typename VectorType::iterator b=result.begin(), e=result.end();
  int i=0;
  while(b!=e)
  {
    *b = m_trees(i)->operator()(0);
    ++b;
    ++i;
  }
  if(m.numberOfRows()!=dimension() || m.numberOfColumns()!= dimension())
    throw std::runtime_error("CnMap::operator()(const VectorType&, MatrixType&): incorrect dimension of the matrix");

  typename MatrixType::iterator mb=m.begin(), me=m.end();
  i=0;
  while(mb!=me)
  {
    typename TreesContainer::const_iterator b1=m_trees.begin(i,1), e1=m_trees.end(i,1);
    while(b1!=e1)
    {
      *mb = (*b1)->operator()(0);
      ++mb;
      ++b1;
    }
    ++i;
  }
  return result;
}

template<typename MatrixT, int rank>
typename CnMap<MatrixT,rank>::CnCoeffType CnMap<MatrixT,rank>::operator()(const CnCoeffType & x) const{
  if( (x.dimension()!=dimension()) ){
    throw std::runtime_error("CnMap:: Jet propagation - Incompatible dimensions of CnCoeff and CnMap");
  }
  if( x.rank()>getRank() ){
    throw std::runtime_error("CnMap:: Jet propagation - Rank is too big");
  }
  CnCoeffType df(x.dimension(),x.rank()),
      result(x.dimension(),x.rank());
  this->computeDerivatives(x(),df,0);
  substitutionPowerSeries(df,x,result,false);
  return result;
}

/*___________________________________________*/

template<typename MatrixT, int rank>
typename CnMap<MatrixT,rank>::VectorType
  CnMap<MatrixT,rank>::operator()(const VectorType& v, int r) const
{
  setArgument(v,r);
  VectorType result(dimension());
  typename VectorType::iterator b=result.begin(), e=result.end();
  int i=0;
  while(b!=e)
  {
    *b = m_trees(i)->operator()(r);
    ++b;
    ++i;
  }
  return result;
}

/*___________________________________________*/

template<typename MatrixT, int rank>
void CnMap<MatrixT,rank>::createFromText(std::string a_s)
{
  Parser::removeWhiteSpaces(a_s);
  int i, j;
  std::vector<std::string> fun;
  Parser::splitVariables("fun:",a_s,fun);
  m_dim2 = fun.size();

  m_trees = TreesContainer(m_dim2,getRank());
  m_formulas = CnContainer<std::string>(m_dim2,getRank());

  for(i=0;i<m_dim2;++i)
  {
    m_formulas(i) = fun[i];
    m_currentFormula = &(m_formulas(i));
    eqnanal(fun[i],& (m_trees(i)));
    (m_trees(i)->m_links)++;
  }

  // now we compute the partial derivatives up to the order 'rank'
  // for k=1
  if(getRank()>0)
  {
    for(i=0;i<m_dim2;++i)
    {
      m_currentFormula = & (m_formulas(i));
      for(j=0;j<m_dim2;++j)
      {
        std::string temp = *m_currentFormula;
        m_formulas(i,j) = diffanal(temp,j);
        if(m_formulas(i,j)=="") m_formulas(i,j)="0";
        eqnanal(m_formulas(i,j), &(m_trees(i,j)));
        (m_trees(i,j)->m_links)++;
      }
    }
  }

  // for k>1
  for(i=2;i<=getRank();++i)
  {
    typename TreesContainer::Multipointer mp = m_trees.first(i);
    do{
      typename TreesContainer::Multipointer mp2(i-1,mp.begin());
      for(j=0;j<m_dim2;++j)
      {
        std::string temp = m_formulas(j,mp2);
        m_formulas(j,mp) = diffanal(temp,mp[mp.dimension()-1]);
        if(m_formulas(j,mp)=="") m_formulas(j,mp)="0";
        m_currentFormula = &(m_formulas(j,mp));
        eqnanal(m_formulas(j,mp),&(m_trees(j,mp)));
        (m_trees(j,mp)->m_links)++;
      }
    }while(m_trees.next(mp));
  }
}

/*___________________________________________*/

template<typename MatrixT, int rank>
void CnMap<MatrixT,rank>::createFromObject(const CnMap& a_m)
{
  m_formulas = a_m.m_formulas;
  m_dim2 = a_m.m_dim2;
  m_trees = TreesContainer(m_dim2,getRank());

  typename TreesContainer::iterator b=m_trees.begin(), e=m_trees.end();
  typename CnContainer<std::string>::iterator i=m_formulas.begin();

  while(b!=e)
  {
    m_currentFormula = &(*i);
    eqnanal(*m_currentFormula,&(*b));
    ((**b).m_links)++;
    ++b;
    ++i;
  }
}

/*___________________________________________*/

template<typename MatrixT,int rank>
CnMap<MatrixT,rank>::CnMap(void) : m_trees(1,1), m_formulas(1,1)
{
  m_dim2=1;
  m_trees(0) = new ConsNode<ScalarType>(m_order,ScalarType(0));
  m_trees(0,0) = new ConsNode<ScalarType>(m_order,ScalarType(0));
  (m_trees(0)->m_links)++;
  (m_trees(0,0)->m_links)++;
}

/*___________________________________________*/

template<typename MatrixT, int rank>
CnMap<MatrixT,rank>::CnMap(const char* s, int order)
  : BasicFunction<ScalarType>(s,order), m_trees(1,1), m_formulas(1,1)
{
  createFromText(s);
}

/*___________________________________________*/

template<typename MatrixT, int rank>
CnMap<MatrixT,rank>::CnMap(const std::string& s, int order)
  : BasicFunction<ScalarType>(s,order), m_trees(1,1), m_formulas(1,1)
{
  createFromText(s);
}

/*_____________________________________________*/

template<typename MatrixT, int rank>
CnMap<MatrixT,rank>& CnMap<MatrixT,rank>::operator=(const char* s)
{
  BasicFunction<ScalarType>::operator=(s);
  deleteTables();
  createFromText(s);
  return *this;
}

/*_______________________________________________*/

template<typename MatrixT, int rank>
CnMap<MatrixT,rank>& CnMap<MatrixT,rank>::operator=(const std::string& s)
{
  BasicFunction<ScalarType>::operator=(s);
  deleteTables();
  createFromText(s);
  return *this;
}

/*________________________________________________*/

template<typename MatrixT, int rank>
CnMap<MatrixT,rank>& CnMap<MatrixT,rank>::operator=(const CnMap& a_m)
{
  if(this != &a_m)
  {
    BasicFunction<ScalarType>::operator=(a_m);
    deleteTables();
    createFromObject(a_m);
  }
  return *this;
}

/*________________________________________________*/


template<typename MatrixType,int rank>
void CnMap<MatrixType,rank>::setOrder(int a_order)
{
  BasicFunction<ScalarType>::setOrder(a_order);

  typename TreesContainer::iterator b=m_trees.begin(), e=m_trees.end();
  while(b!=e)
  {
    (*b)->setOrder(m_order,m_val);
    ++b;
  }
}

/*________________________________________________*/

template<typename MatrixType, int rank>
void CnMap<MatrixType,rank>::deleteTables()
{
  typename TreesContainer::iterator b = m_trees.begin(), e=m_trees.end();
  while(b!=e)
  {
    if( !( --(**b).m_links) )
      delete (*b);
    ++b;
  }
}

/*________________________________________________*/

template <typename MatrixType, int rank>
CnMap<MatrixType,rank>::~CnMap()
{
  deleteTables();
}

/*________________________________________________*/

template <typename MatrixType, int rank>
void CnMap<MatrixType,rank>::getMask(capd::map::CnContainer<bool>& result) const
{
  if(result.dimension()!=dimension() || result.rank() != rank)
    throw std::runtime_error("CnMap::getMask - incompatible dimension or rank");

  capd::map::CnContainer<bool>::iterator i = result.begin();
  typename TreesContainer::const_iterator b = m_trees.begin(), e = m_trees.end();
  while(b!=e)
  {
    if( (*b)->isConst() )
    {
      if((*b)->operator[](0)==ScalarType(0))
        (*i) = true;
      else (*i) = false;
    } else
      (*i) = false;
    ++b;
    ++i;
  }
}

}} // namespace capd::map

#endif // _CAPD_MAP_CNMAP_HPP_

/// @}
