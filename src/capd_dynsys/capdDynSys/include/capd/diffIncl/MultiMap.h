/// @addtogroup diffIncl
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file MultiMap.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Tomasz Kapela, 2007 */

#ifndef _CAPD_DIFFINCL_MULTIMAP_H_ 
#define _CAPD_DIFFINCL_MULTIMAP_H_ 

#include <string>
#include <map>
#include <vector>
#include "capd/vectalg/Norm.h"


namespace capd{
namespace diffIncl{

/////////////////////////////////////////////////////////////////////////////////
// MultiMap 
///
///  A multi map for differential inclusions
///
/// We assume that map is in the form
///   \f$ f(x,e) = f(x) + g(x,epsilon) \f$ 
/// where epsilon is some interval set,
/// e0 is contained in epsilon
/// and g(x,e0) = 0
///
/// This form is needed to  estimate  the perturbations better
/////////////////////////////////////////////////////////////////////////////////
template<typename FMapT, typename GMapT = FMapT>
class MultiMap{

public:
  typedef FMapT MapType;
  typedef GMapT PerturbationType;
  typedef typename MapType::FunctionType FunctionType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef std::vector<ScalarType> ParamType;

  MultiMap( MapType & Field,
      PerturbationType & Perturb
  ) : m_f(&Field), m_g(&Perturb) {
  }


  /// value of MultiMap
  VectorType operator()(const VectorType & X) const {
    return (*m_f)(X) + (*m_g)(X);
  }

  /// derivative  of a MultiMap
  MatrixType operator[](const VectorType & X) const {
    return (*m_f)[X] + (*m_g)[X];

  }

  /// value and derivative of a MultiMap
  VectorType operator()(const VectorType & X, MatrixType &dF) const{
    dF = (*m_f)[X] + (*m_g)[X];
    return (*m_f)(X) + (*m_g)(X);
  }

  MapType & getVectorField(){
    return *m_f;
  }
  const MapType & getVectorField() const{
    return *m_f;
  }

  PerturbationType & getPerturbations(){
    return *m_g;
  }

  const PerturbationType & getPerturbations() const{
    return *m_g;
  }

  VectorType perturbations(VectorType const & X){
    return (*m_g)(X);
  }

  int dimension() const{
    return m_f->dimension();
  }

  /// deprecate: use dimension() instead
  int getDimension() const{
    return dimension();
  }

  const MultiMap & operator=(const MultiMap & map){
    m_f = map.m_f;
    m_g = map.m_g;
    return *this;
  }

protected:
  MapType * m_f;              ///< vector field 
  PerturbationType * m_g;     ///< perturbations of the vector field
};



}} // namespace capd::diffIncl

#endif // _CAPD_DIFFINCL_MULTIMAP_H_ 

/// @}
