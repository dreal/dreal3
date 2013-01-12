/// @addtogroup diffIncl
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file InclRect2Set.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2007 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_DIFFINCL_INCLRECT2SET_H_ 
#define _CAPD_DIFFINCL_INCLRECT2SET_H_ 

//#include "dynset/inclc0set.h"
#include "capd/dynset/C0Rect2Set.h"
#include "capd/dynset/ReorganizedSet.h"
#include "capd/vectalg/Norm.h"

namespace capd{
namespace diffIncl{

///////////////////////////////////////////////////////////////////////////
// InclRect2Set
/// 
/// Set representation for differential inclusions based on capd::dynset::Rect2Set class
///
///   set is represented as: x + C*r0 + B*r   where
///       C*r0 - basic 'Lipschitz part'
///       B*r - QR-decomposition of the remaining errors
///   

template<typename MatrixT>
class InclRect2Set : public capd::dynset::ReorganizedSet< capd::dynset::C0Rect2Set<MatrixT> >{

public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::dynset::ReorganizedSet< capd::dynset::C0Rect2Set<MatrixT> > BaseSet;

  // constr
  explicit InclRect2Set(int dimension);
  explicit InclRect2Set(const VectorType& the_x);
  InclRect2Set(const VectorType& the_x, const VectorType& the_r0);
  InclRect2Set(const VectorType& the_x, const MatrixType& the_C, const VectorType& the_r0);
  InclRect2Set(const VectorType& the_x, const MatrixType& the_C,
               const VectorType& the_r0,
               const VectorType& the_r
  );
  
  capd::dynset::C0Set<MatrixType>* clone(void) const;
  capd::dynset::C0Set<MatrixType>* fresh(void) const;
  capd::dynset::C0Set<MatrixType>* cover(const VectorType& v) const;
  
  template<typename DiffIncl>
  void move( DiffIncl& dynsys);
  template<typename DiffIncl>
  void move( DiffIncl & dynsys, InclRect2Set& result) const;
  
  std::vector<VectorType> getCorners() const;

  using BaseSet::get_x;
  using BaseSet::get_r;
  using BaseSet::get_r0;
  using BaseSet::get_B;
  using BaseSet::get_C;
  using BaseSet::operator VectorType;
  using BaseSet::show;
  using BaseSet::affineTransformation;

protected:
  using BaseSet::m_x;
  using BaseSet::m_r;
  using BaseSet::m_r0;
  using BaseSet::m_B;
  using BaseSet::m_C;
};

template<typename MatrixType>
std::vector<typename MatrixType::VectorType> getCorners(const InclRect2Set<MatrixType> & set) ;

// inline definitions
////////////////////////////////////////////////////////////////////////////////
/// Constructors
template<typename MatrixType>
inline InclRect2Set<MatrixType>::InclRect2Set(int dim)
  :  BaseSet(dim) {
}

template<typename MatrixType>
inline InclRect2Set<MatrixType>::InclRect2Set(const VectorType& the_x)
  :  BaseSet(the_x) {
}

template<typename MatrixType>
inline InclRect2Set<MatrixType>::InclRect2Set(const VectorType& the_x,const VectorType& the_r0)
  :  BaseSet(the_x, the_r0) {
}

template<typename MatrixType>
inline InclRect2Set<MatrixType>::InclRect2Set(
      const VectorType& the_x,
      const MatrixType& the_C,
      const VectorType& the_r0
   )
  : BaseSet(the_x, the_C, the_r0){
}

template<typename MatrixType>
inline InclRect2Set<MatrixType>::InclRect2Set(
      const VectorType& the_x,
      const MatrixType &the_C,
      const VectorType& the_r0,
      const VectorType& the_r
   ): BaseSet(the_x, the_C, the_r0, the_r){
}

////////////////////////////////////////////////////////////////////////////////
/// C0set interface overriding
   
template<typename MatrixType>
inline typename capd::dynset::C0Set<MatrixType>* InclRect2Set<MatrixType>::clone() const{
   return new InclRect2Set(*this);
}

template<typename MatrixType>
inline typename capd::dynset::C0Set<MatrixType>* InclRect2Set<MatrixType>::fresh() const{
   return new InclRect2Set<MatrixType>(m_x.dimension());
}

template<typename MatrixType>
inline typename capd::dynset::C0Set<MatrixType>* InclRect2Set<MatrixType>::cover(const VectorType& v) const{
   return new InclRect2Set(midVector(v),v-midVector(v));
}
////////////////////////////////////////////////////////////////////////////////
template<typename MatrixType>
std::vector<typename MatrixType::VectorType> getCorners(const capd::diffIncl::InclRect2Set<MatrixType> & set) ;

}} // namespace capd::diffIncl

#endif // _CAPD_DIFFINCL_INCLRECT2SET_H_ 

/// @}
