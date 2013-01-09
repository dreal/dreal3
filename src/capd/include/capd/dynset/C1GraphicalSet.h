/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C1GraphicalSet.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.


#ifndef _CAPD_DYNSET_C1GraphicalSet_H_
#define _CAPD_DYNSET_C1GraphicalSet_H_

#include "capd/dynset/C1Set.h"
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/C1DynSys.h"


namespace capd{
namespace dynset{
///////////////////////////////////////////////////////////////////////////////////
/// C1GraphicalSet is an envelope class for any class derived from C1Set.
/// It adds a possibility of an additional Output after each 'move' of the original set.
///
///  OutputClass only need to implement function
///    void show(C1Set & set)
///  which can e.g. draw on a screen or log set position to a file.
//////////////////////////////////////////////////////////////////////////////////
template<typename MatrixT, typename OutputClass>
class C1GraphicalSet : public C1Set<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::dynset::C1Set<MatrixType> SetType;
  typedef OutputClass Output;

  C1GraphicalSet(SetType * pSet, Output * output) : m_set(pSet), m_output(output){
  }
  C1GraphicalSet(SetType & set, Output & output) : m_set(&set), m_output(&output){
  }
  C1GraphicalSet(const C1GraphicalSet &c){
    m_set = c.m_set->clone();
    m_output = c.m_output;
  }
  /// Destructor do not delete any objects (they can be shared), it up to user if they are static or dynamic
  ~C1GraphicalSet(){
  }

  ScalarType size(void) const{
  return m_set->size();
  }
  C1Set<MatrixType>* clone(void) const {
    return new C1GraphicalSet(m_set->clone(), m_output);
  }
  C1Set<MatrixType>* fresh(void) const {
  return new C1GraphicalSet(m_set->fresh(), m_output);
  }
  C1Set<MatrixType>* cover(const VectorType& v) const {
  return new C1GraphicalSet(m_set->cover(v), m_output);
  }

  VectorType center(void) const {
  return m_set->center();
  }
  void move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys){
    m_set->move(c1dynsys);
    m_output->show(*m_set);

  }
  void move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys, C1GraphicalSet& result) const{
    m_set->move(c1dynsys, result);
    m_output->show(result);
  }

  std::string show(void) const{
    return m_set->show();
  }
  const NormType* getNorm(void) const{
    return m_set->getNorm();
  }

  operator VectorType() const{
    return static_cast<VectorType>(*m_set);
  }
  operator MatrixType() const{
    return static_cast<MatrixType>(*m_set);
  }
  C1GraphicalSet &operator=(const VectorType &v){
    (*m_set) = v;
    return *this;
  }
  C1GraphicalSet &operator=(const C1GraphicalSet &S){
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
}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_C1GraphicalSet_H_

/// @}
