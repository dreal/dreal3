/////////////////////////////////////////////////////////////////////////////
/// @file C0GraphicalSet.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.


#ifndef _CAPD_DYNSET_C0GRAPHICALSET_H_
#define _CAPD_DYNSET_C0GRAPHICALSET_H_

#include "capd/dynset/C0Set.h"
#include "capd/dynsys/DynSys.h"


namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

///////////////////////////////////////////////////////////////////////////////////
/// C0GraphicalSet is an envelope class for any class derived from C0Set.
/// It adds a possibility of an additional Output after each 'move' of the original set.
///
///  Output only needs to implement function
///    void show(C0Set & set)
///  which can e.g. draws on a screen or logs the set position to a file.
//////////////////////////////////////////////////////////////////////////////////
template<typename MatrixT, typename OutputT>
class C0GraphicalSet : public C0Set<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  /// @}
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::dynset::C0Set<MatrixType> SetType;
  typedef OutputT Output;

  C0GraphicalSet(SetType * pSet, Output * output) : m_set(pSet), m_output(output){
  }
  C0GraphicalSet(SetType & set, Output & output) : m_set(&set), m_output(&output){
  }
  C0GraphicalSet(const C0GraphicalSet &c){
    m_set = c.m_set->clone();
    m_output = c.m_output;
  }
  /// Destructor do not delete any objects (they can be shared), it up to user if they are static or dynamic
  ~C0GraphicalSet(){
  }

  ScalarType size(void){
    return m_set->size();
  }
  C0Set<MatrixType>* clone(void) {
    return new C0GraphicalSet(m_set->clone(), m_output);
  }
  C0Set<MatrixType>* fresh(void) {
    return new C0GraphicalSet(m_set->fresh(), m_output);
  }

  C0Set<MatrixType>* cover(const VectorType& v) {
    return new C0GraphicalSet(m_set->cover(v), m_output);
  }

  VectorType center(void) {
    return m_set->center();
  }

  void move(capd::dynsys::DynSys<MatrixType>& dynsys){
    m_set->move(dynsys);
    m_output->show(*m_set);
  }

  template<class ResultType>
  void move(capd::dynsys::DynSys<MatrixType>& dynsys, ResultType& result){
    ResultType* set = dynamic_cast<ResultType*>(m_set);
    set->move(dynsys,result);
    m_output->show(result);
  }

  VectorType affineTransformation(const MatrixType& A, const VectorType& v) const {
    return m_set->affineTransformation(A, v);
  }

  std::string show(void) const{
    return m_set->show();
  }

  operator VectorType() const{
    return static_cast<VectorType>(*m_set);
  }

  C0GraphicalSet &operator=(const VectorType &v){
    (*m_set) = v;
    return *this;
  }
  C0GraphicalSet &operator=(const C0GraphicalSet &S){
    m_set = S.m_set;
    m_output = S.m_output;
    return *this;
  }
  SetType & getSet(){
    return *m_set;
  }
  Output & getOutput(){
    return *m_output();
  }
protected:
  SetType * m_set;
  Output * m_output;

};
/// @}

}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_C0GRAPHICALSET_H_

