/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnRect2.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_CNRECT2_H_ 
#define _CAPD_DYNSET_CNRECT2_H_ 

#include <stdexcept>
#include "capd/dynset/CnSet.h"
#include "capd/map/CnCoeff.h"

namespace capd{
namespace dynset{

template<typename MatrixT>
class CnRect2 : public CnSet<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef capd::map::CnCoeff<MatrixType> CnCoeffType;
  typedef CnSet<MatrixT> CnSetType;
  typedef typename CnSetType::VectorType VectorType;
  typedef typename CnSetType::ScalarType ScalarType;
  typedef typename CnSetType::RefVectorType RefVectorType;
  typedef typename CnSetType::NormType NormType;
  typedef typename CnSetType::Multipointer Multipointer;
  typedef typename CnSetType::Multiindex Multiindex;

  // constructors
  CnRect2(const VectorType& x, const NormType&, int rank, double sizeFactor = 20.);
  CnRect2(const VectorType& x, const MatrixType& C, const VectorType& r, const NormType&, int rank, double sizeFactor = 20.);
  CnRect2(const CnRect2&);
  ~CnRect2(){ delete m_norm; } 

  CnRect2& operator=(const CnRect2&);
  CnRect2& operator=(const VectorType&); 
  void move(capd::dynsys::CnDynSys<MatrixType>& cndynsys) { this->move(cndynsys,*this); } 
  void move(capd::dynsys::CnDynSys<MatrixType>& cndynsys, CnRect2& result) const;
   
  inline CnSetType* clone(void) const { return new CnRect2(*this); }
  inline ScalarType size(void) const { return capd::vectalg::size(m_currentSet()); }
  inline VectorType center(void) const { return VectorType(m_x); }
  inline const NormType* getNorm(void) const { return m_norm; } 

  inline operator VectorType() const { return VectorType(m_currentSet); }
  inline operator MatrixType() const { return MatrixType(m_currentSet); } 

  // this operator returns a vector of partial derivatives, i.e. result[i] = d^{mp}f_i
  inline RefVectorType operator()(const Multipointer& mp) const { return m_currentSet(mp); } 

  // this operators returns d^{mp}f_i
  inline const ScalarType& operator()(int i,const Multiindex& mp) const { return m_currentSet(i,mp); } 
  inline const ScalarType& operator()(int i,const Multipointer& mp) const { return m_currentSet(i,mp); } 


  inline const CnCoeffType& currentSet() const { return m_currentSet; }
  inline CnCoeffType& currentSet() { return m_currentSet; }
  // indexing for C^3
  inline const ScalarType& operator()(int i, int j, int c, int k) const { return m_currentSet(i,j,c,k); }
  inline ScalarType& operator()(int i, int j, int c, int k) { return m_currentSet(i,j,c,k); }
  // indexing for C^2
  inline const ScalarType& operator()(int i, int j, int c) const { return m_currentSet(i,j,c); }
  inline ScalarType& operator()(int i, int j, int c) { return m_currentSet(i,j,c); }
  // indexing for C^1
  inline const ScalarType& operator()(int i, int j) const { return m_currentSet(i,j); } 
  inline ScalarType& operator()(int i, int j) { return m_currentSet(i,j); } 
  // indexing for C^0
  inline const ScalarType& operator()(int i) const {return m_currentSet(i); }
  inline ScalarType& operator()(int i) {return m_currentSet(i); }

  inline int getRank() const { return m_x.rank(); } 
  inline int getDimension() const { return m_x.dimension(); }

private:
  CnCoeffType m_x,
              m_r,
              m_r0,
              m_currentSet;
  MatrixType m_B,m_C;
  MatrixType m_Bjac, m_Cjac;
  double m_sizeFactor;
  NormType* m_norm;
}; // end of class CnRect2

}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_CNRECT2_H_ 

/// @}
