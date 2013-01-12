/*
 * DoubletonSetSpecyfic.hpp
 *
 *  Created on: Oct 17, 2009
 *      Author: kapela
 */

#ifndef DOUBLETONSETSPECYFIC_HPP_
#define DOUBLETONSETSPECYFIC_HPP_
BOOST_AUTO_TEST_CASE(test_constructors1){
  SetType::VectorType v(2);
  v[0] = SetType::ScalarType(-1,1); v[1] = SetType::ScalarType(-1,3);
  SetType T(v);
  v[0] = 0.; v[1] = 1;
  BOOST_CHECK_EQUAL(v,T.get_x());
  v[0]= SetType::ScalarType(-1,1);
  v[1]= SetType::ScalarType(-2,2);
  BOOST_CHECK_EQUAL(v,T.get_r0());
}

#endif /* DOUBLETONSETSPECYFIC_HPP_ */
