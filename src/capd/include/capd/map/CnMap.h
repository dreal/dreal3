/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnMap.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak  2006 */

#ifndef _CAPD_MAP_CNMAP_H_ 
#define _CAPD_MAP_CNMAP_H_ 

#include <string>
#include <stdexcept>
#include <sstream>
#include <vector>

#include "capd/map/BasicFunction.h"
#include "capd/map/Function.h"
#include "capd/map/C2Coeff.h"
#include "capd/map/CnCoeff.h"
#include "capd/map/SeriesContainer.h"

namespace capd{
namespace map{

// ----------------------------------------------

template<typename MatrixT, int rank=1>
class CnMap : protected BasicFunction<typename MatrixT::ScalarType>
{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename VectorType::ScalarType ScalarType;
  typedef Function<VectorType> FunctionType;
  typedef Node<ScalarType> NodeType;
  typedef ConsNode<ScalarType> ConsNodeType;
  typedef C2Coeff<ScalarType> C2CoeffType;
  typedef CnCoeff<MatrixType> CnCoeffType;
  typedef CnContainer<NodeType*> TreesContainer;
  typedef capd::map::SeriesContainer<ScalarType> SeriesContainerType;

  CnMap(void);
  CnMap(const std::string &, int order=0);
  CnMap(const char *, int order=0);
  CnMap(const CnMap&);
  ~CnMap();

  CnMap& operator=(const char *);
  CnMap& operator=(const std::string &);
  CnMap& operator=(const CnMap&);
  void computeDerivatives(const VectorType& v, CnCoeffType& result, int r=0) const;
  void computeDerivatives(const VectorType& v, const SeriesContainerType& result, int order, int minRank, int maxRank) const;
  void getMask(capd::map::CnContainer<bool>& result) const;
   
// to be compatible with Map and C2Map interfaces
// from class Map
  VectorType operator()(const VectorType &, int = 0) const;
  VectorType operator()(const VectorType &, MatrixType &) const;
  /// computes propagation of the jet x through map
  CnCoeffType  operator()(const CnCoeffType & x) const;
  MatrixType operator[](const VectorType &) const;
  //const FunctionType& operator()(int) const;
  void variational(VectorType[], MatrixType[], int i) const;

// from class C2Map
  C2CoeffType* computeSecondDerivatives(VectorType [], int) const;
  void computeSecondDerivatives(const VectorType &v, C2CoeffType &result) const;

  int dimension() const {return m_dim2;}
  int getRank() const {return rank;}
  int getOrder() const {return m_order;}
  void setOrder(int);

  using BasicFunction<ScalarType>::setParameter;
  using BasicFunction<ScalarType>::variables;

  void differentiateTime() const
  {
    BasicFunction<ScalarType>::differentiateTime(m_dim2);
  }

  void setCurrentTime(const ScalarType& a_time) const
  {
    BasicFunction<ScalarType>::setCurrentTime(a_time,m_dim2);
  }

  const ScalarType& getCurrentTime() const
  {
    return BasicFunction<ScalarType>::getCurrentTime(m_dim2);
  }

protected:
  TreesContainer m_trees;
  CnContainer<std::string> m_formulas;
  int m_dim2;
  std::string* m_currentFormula;
  const std::string& currentFormula();
   
  using BasicFunction<ScalarType>::m_dim;
  using BasicFunction<ScalarType>::m_order;
  using BasicFunction<ScalarType>::m_val;
  using BasicFunction<ScalarType>::m_var;
  using BasicFunction<ScalarType>::m_size;
  using BasicFunction<ScalarType>::diffanal;
  using BasicFunction<ScalarType>::eqnanal;

private:
  void setArgument(const VectorType& v, int j=0) const;
  void createFromText(std::string );
  void createFromObject(const CnMap&);
  void deleteTables();
  void reset() const;
}; // the end of class CnMap

// ---------------------------- inline definitions ------------------

template<typename MatrixT, int rank>
inline CnMap<MatrixT,rank>::CnMap(const CnMap& a_m) 
  : BasicFunction<ScalarType>(a_m), m_trees(1,1), m_formulas(1,1)
{
  createFromObject(a_m);
}

template<typename MatrixT, int rank>
inline const std::string& CnMap<MatrixT,rank>::currentFormula()
{
  return *m_currentFormula;
}

}} // the end of the namespace capd::map

#endif // _CAPD_MAP_CNMAP_H_ 

/// @}
