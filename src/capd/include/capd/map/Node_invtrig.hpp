//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file Node_atan.hpp
///
/// @author Tomasz Kapela   @date 2010-02-26
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_MAP_NODE_ATAN_HPP_
#define _CAPD_MAP_NODE_ATAN_HPP_

namespace capd {
namespace map {

template <typename ScalarType>
ScalarType& AtanNode<ScalarType>::operator()(int k) {
  if(k > this->m_maxComputedDerivative) {

    this->m_maxComputedDerivative = k;

    (*(this->left))(k);
    (*(this->right))(k);

    if(k == 0) {
      return this->value[0] = atan(this->left->value[0]);
    }

    ScalarType result(0.);
    for(int j = 1; j < k; j++) {
      result += j * this->value[j] * this->right->value[k - j];
    }
    this->value[k] = (this->left->value[k] - result / ScalarType(k))
        / this->right->value[0];
  }
  return this->value[k];
}

template <typename ScalarType>
ScalarType& AsinNode<ScalarType>::operator()(int k) {
  if(k > this->m_maxComputedDerivative) {

    this->m_maxComputedDerivative = k;

    (*(this->left))(k);
    (*(this->right))(k);

    if(k == 0) {
      return this->value[0] = asin(this->left->value[0]);
    }

    ScalarType result(0.);
    for(int j = 1; j < k; j++) {
      result += j * this->value[j] * this->right->value[k - j];
    }
    this->value[k] = (this->left->value[k] - result / ScalarType(k))
        / this->right->value[0];
  }
  return this->value[k];
}

template <typename ScalarType>
ScalarType& AcosNode<ScalarType>::operator()(int k) {
  if(k > this->m_maxComputedDerivative) {

    this->m_maxComputedDerivative = k;

    (*(this->left))(k);
    (*(this->right))(k);

    if(k == 0) {
      return this->value[0] = acos(this->left->value[0]);
    }

    ScalarType result(0.);
    for(int j = 1; j < k; j++) {
      result += j * this->value[j] * this->right->value[k - j];
    }
    this->value[k] = -(this->left->value[k] - result / ScalarType(k))
        / this->right->value[0];
  }
  return this->value[k];
}

}
} // end of namespace capd::map

#endif // _CAPD_MAP_NODE_ATAN_HPP_
