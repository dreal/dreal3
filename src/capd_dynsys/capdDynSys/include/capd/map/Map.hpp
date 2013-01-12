/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Map.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2001-2004 */

#ifndef _CAPD_MAP_MAP_HPP_ 
#define _CAPD_MAP_MAP_HPP_ 

#include <string>
#include <sstream>
#include <stdexcept>
#include <vector>
#include "capd/map/Function.hpp"
#include "capd/map/Node.hpp"
#include "capd/map/Parser.h"
#include "capd/map/Map.h"

namespace capd{
namespace map{

template<typename MatrixType>
void Map<MatrixType>::setCurrentTime(const ScalarType& a_time) const
{
  int i;
  for(i=0;i<m_dim;++i)
    m_fun[i].setCurrentTime(a_time,m_dim);

  for(i=0;i<m_dim*m_dim;++i)
    m_der[i].setCurrentTime(a_time,m_dim);
}

/*___________________________________________*/

template<typename MatrixType>
void Map<MatrixType>::differentiateTime() const
{
  int i;
  for(i=0;i<m_dim;++i)
    m_fun[i].differentiateTime(m_dim);

  for(i=0;i<m_dim*m_dim;++i)
    m_der[i].differentiateTime(m_dim);
}

/*___________________________________________*/

template<typename MatrixType>
void Map<MatrixType>::createFromText(const std::string &s, int a_order)
{
  std::vector<std::string> tab;
  Parser::splitVariables("fun:",s,tab);
  m_dim = tab.size();
  size_t funPos = s.find("fun:");
  std::string variables = s.substr(0,funPos);
  variables += "fun:";

  m_fun = new FunctionType[m_dim];
  m_der = new FunctionType[m_dim*m_dim];
  m_order = a_order;

  int i,j;
  for(i=0;i<m_dim;++i)
  {
    m_fun[i] = variables + tab[i] + ";";
    m_fun[i].setOrder(m_order);
  }

  for(i=0;i<m_dim;++i)
    for(j=0;j<m_dim;++j)
    {
      m_der[i*m_dim+j]=m_fun[i][j];
      m_der[i*m_dim+j].setOrder(m_order);
    }
}

/*___________________________________________*/

template<typename MatrixType>
void Map<MatrixType>::createFromObject(const Map<MatrixType> &m)
{
  m_dim = m.m_dim;
  m_fun = new FunctionType[m_dim];
  m_der = new FunctionType[m_dim*m_dim];
  int i;
  for(i=0;i<m_dim;++i)
    m_fun[i] = m.m_fun[i];

  for(i=0;i<m_dim*m_dim;++i)
    m_der[i] = m.m_der[i];
  m_order = m.m_order;
}

/*___________________________________________*/

template<typename MatrixType>
Map<MatrixType>::Map(void)
{
  m_order=0;
  m_dim = 1;
  m_fun = new FunctionType[m_dim];
  m_der = new FunctionType[m_dim];
}

/*___________________________________________*/

template<typename MatrixType>
Map<MatrixType>::Map(const char *s, int order)
{
  try{
    createFromText(s,order);
  } catch(std::runtime_error &r)
  {
    std::string re = "exception in constructor Map::Map(const char *, int)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
}

/*___________________________________________*/

template<typename MatrixType>
Map<MatrixType>::Map(const std::string &f, int order)
{
  try{
    createFromText(f,order);
  } catch(std::runtime_error &r)
  {
    std::string re = "exception in constructor Map::Map(const string&, int)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
}

/*___________________________________________*/

template<typename MatrixType>
Map<MatrixType>::Map(const Map<MatrixType> &m)
{
  createFromObject(m);
}

/*_____________________________________________*/

template<typename MatrixType>
Map<MatrixType>& Map<MatrixType>::operator=(const char *s)
{
  delete []m_fun;
  delete []m_der;

  try{
    createFromText(s,0);
  } catch(std::runtime_error &r)
  {
    std::string re = "exception in Map &Map::operator=(const char *)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
   return *this;
}

/*_______________________________________________*/

template<typename MatrixType>
Map<MatrixType>& Map<MatrixType>::operator=(const std::string &f)
{
  delete []m_fun;
  delete []m_der;
  try{
    createFromText(f,0);
  } catch(std::runtime_error &r)
  {
    std::string re = "exception in Map &Map::operator=(const string &f)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
  return *this;
}

/*________________________________________________*/

template<typename MatrixType>
Map<MatrixType>& Map<MatrixType>::operator=(const Map<MatrixType> &m)
{
  delete []m_fun;
  delete []m_der;
  createFromObject(m);
  return *this;
}


/*________________________________________________*/

template<typename MatrixType>
MatrixType Map<MatrixType>::operator[](const VectorType &v) const
{
  MatrixType res(m_dim,m_dim);
  for(int i=0;i<m_dim;++i)
    for(int j=0;j<m_dim;++j)
      res[i][j] = m_der[i*m_dim+j](v);
  return res;
}


/*________________________________________________*/


template<typename MatrixType>
void Map<MatrixType>::setOrder(int the_new)
{
  m_order = the_new;
  int i;
  for(i=0;i<m_dim;++i)
    m_fun[i].setOrder(m_order);
  
  for(i=0;i<m_dim*m_dim;++i)
    m_der[i].setOrder(m_order);
}


/*________________________________________________*/

template<typename MatrixType>
void Map<MatrixType>::variational(VectorType iv[], MatrixType im[], int p) const
{
  if(p<0)
  {
    throw std::out_of_range ("exception in void Map::variational(vectorType iv[], matrixType im[], int p)\nnegative index of Taylor coefficient");
  }

  if(p>m_order)
  {
    std::ostringstream s;
    s << "exception in void Map::variational(vectorType iv[], matrixType im[], int p)\n";
    s << "Cannot compute " << p << "-th Taylor coefficient\n";
    s << "The order is " << m_order;
    throw std::out_of_range (s.str());
  }

  for(int i=0;i<m_dim;++i)
    for(int j=0;j<m_dim;++j)
      for(int r=0;r<=p;++r)
        im[r][i][j] = m_der[i*m_dim+j](iv[r],r);
}

/*________________________________________________*/

template<typename MatrixType>
void Map<MatrixType>::setParameter(const std::string &name, const ScalarType &value)
{
  for(int i=0;i<m_dim;++i)
  {
    m_fun[i].setParameter(name,value);
    for(int j=0;j<m_dim;++j)
      m_der[i*m_dim+j].setParameter(name,value);
  }
}

/*________________________________________________*/

template<typename MatrixType>
void Map<MatrixType>::setParameters(const VectorType &values)
{
  for(int i=0;i<m_dim;++i)
  {
    m_fun[i].setParameters(values);
    for(int j=0;j<m_dim;++j)
      m_der[i*m_dim+j].setParameters(values);
  }
}

/*_______________________________________________*/

template<typename MatrixType>
typename Map<MatrixType>::VectorType Map<MatrixType>::operator()(const VectorType &v, int i) const
{
  VectorType result(m_dim);
  if (i<0)
    return result;
  for(int j=0;j<m_dim;++j)
    result[j] = m_fun[j](v,i);
  return result;
}

}} // namespace capd::map

#endif // _CAPD_MAP_MAP_HPP_ 

/// @}
