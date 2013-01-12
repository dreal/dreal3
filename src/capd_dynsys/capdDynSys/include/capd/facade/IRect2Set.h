
/////////////////////////////////////////////////////////////////////////////
/// @file IRect2Set.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_FACADE_IRECT2SET_H_
#define _CAPD_FACADE_IRECT2SET_H_

#include "capd/dynset/C0Rect2Set.h"
#include "capd/dynset/ReorganizedSet.h"
#include "capd/facade/ITaylor.h"

// set is represented as: x + C*r0 + B*r;
// move - Lohner last method - internal representation
//       C*r0 - basic 'Lipschitz part'
//       B*r - QR-decomposition of the remaining errors

namespace capd{
namespace facade{

class IRect2Set : public capd::dynset::C0Set<IMatrix>
{

public:
  typedef IMatrix MatrixType;
  typedef IVector VectorType;
  typedef DInterval ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::dynset::ReorganizedSet< capd::dynset::C0Rect2Set<IMatrix> > BaseRect2Set;

  VectorType get_x () {
    return m_set.get_x();
  }
  VectorType get_r () {
    return m_set.get_r();
  }
  VectorType get_r0 () {
    return m_set.get_r0();
  }
  
  MatrixType get_B () {
    return m_set.get_B();
  }
  MatrixType get_C () {
    return m_set.get_C();
  }

  IRect2Set(int dim, double sizeFactor = 20) 
      : m_set(dim) {
    m_set.setFactor(sizeFactor);
  }
  explicit IRect2Set(const VectorType& x, double sizeFactor = 20)
    : m_set(x) {
    m_set.setFactor(sizeFactor);
  }
  
  IRect2Set(const VectorType& x, const VectorType& r0, double sizeFactor = 20)
    : m_set(x,r0) {
    m_set.setFactor(sizeFactor);
  }
  
  IRect2Set(const VectorType& x, const MatrixType& C, 
           const VectorType& r0, double sizeFactor = 20
  ) : m_set(x,C,r0) {
    m_set.setFactor(sizeFactor);
  }
  
  IRect2Set(const VectorType& x, const MatrixType& C,
           const VectorType& r0, const VectorType& r, double sizeFactor = 20
  ) : m_set(x,C,r0,r) {
    m_set.setFactor(sizeFactor);
  }

  ScalarType size(void){
    return m_set.size();
  }



  void move(capd::dynsys::DynSys<MatrixType>& dynsys){
    m_set.move(dynsys);
  }
  void move(capd::dynsys::DynSys<MatrixType>& dynsys, IRect2Set& result) const{
    m_set.move(dynsys,result.m_set);
  }
  operator VectorType() const{
    return VectorType(m_set);
  }


  capd::dynset::C0Set<MatrixType>* clone(void){
    return new IRect2Set(*this);
  }
  capd::dynset::C0Set<MatrixType>* fresh(void){
    return new IRect2Set(m_set.get_x().dimension());
  }
  capd::dynset::C0Set<MatrixType>* cover(const VectorType& v){
    return new IRect2Set(v);
  }



  std::string show() const{
    return m_set.show();
  }
  VectorType affineTransformation(const MatrixType& M, const VectorType& u) const{
    return m_set.affineTransformation(M,u);
  }
  void setFactor(double sFactor){
    m_set.setFactor(sFactor);
  }
  void disableSwapping(){
    m_set.disableSwapping();
  }
  double getFactor(){
    return m_set.getFactor();
  }
  
private:
  BaseRect2Set m_set;
};

}} // namespace capd::facade

#endif // _CAPD_FACADE_IRECT2SET_H_

