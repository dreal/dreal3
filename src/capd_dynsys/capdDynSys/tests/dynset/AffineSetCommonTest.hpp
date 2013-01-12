/*
 * SetTypeCommonTest.cpp
 *
 *  Created on: Oct 16, 2009
 *      Author: kapela
 */

#ifndef AFFINESETCOMMONTEST_CPP_
#define AFFINESETCOMMONTEST_CPP_

#define _TESTS_WITHOUT_BOOST_LIB_

#ifdef _TESTS_WITHOUT_BOOST_LIB_

#define BOOST_TEST_MODULE FIXTURE_NAME
#include <boost/test/included/unit_test.hpp>

#else
#define BOOST_TEST_MODULE FIXTURE_NAME
#define BOOST_TEST_MAIN
#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#endif

using namespace boost::unit_test;

//____________________________________________________________________________//

struct MyConfig {
    MyConfig()  { //unit_test_log.set_format( XML );
   //   unit_test_log.set_threshold_level(log_nothing);
    }

    ~MyConfig() {}
};

//____________________________________________________________________________//

BOOST_GLOBAL_FIXTURE( MyConfig );

BOOST_AUTO_TEST_CASE(test_getset_x) {
  SetType set(2);
  SetType::VectorType v(2);
  v[0] = 1; v[1] = 2;
  set.set_x(v);
  BOOST_CHECK_EQUAL(v, set.get_x());
  set.setElement_x(0, SetType::ScalarType(3));
  BOOST_CHECK_NE(v, set.get_x());
  BOOST_CHECK_EQUAL(3,set.getElement_x(0).rightBound());
}

BOOST_AUTO_TEST_CASE(test_getset_r) {
  SetType set(2);
  SetType::VectorType v(2);
  v[0] = 1; v[1] = 2;
  set.set_r(v);
  BOOST_CHECK_EQUAL(v, set.get_r());
  set.setElement_r(0, SetType::ScalarType(3));
  BOOST_CHECK_NE(v, set.get_r());
  BOOST_CHECK_EQUAL(3,set.getElement_r(0).rightBound());
}

BOOST_AUTO_TEST_CASE( test_getset_B) {
  SetType set(2);
  SetType::MatrixType A(2,2);
  A[0][0] = 1; A[0][1] = 2;
  A[1][0] = 3; A[1][1] = 4;
  set.set_B(A);
  BOOST_CHECK_EQUAL(A, set.get_B());
  set.setElement_B(0, 0, SetType::ScalarType(3));
  BOOST_CHECK_NE(A, set.get_B());
  BOOST_CHECK_EQUAL(3,set.getElement_B(0,0).rightBound());
  
  SetType::VectorType v(2);
  v[0] = 5; v[1] = 6;
  set.setColumn_B(1,v);
  set.setRow_B(0,v);
  SetType::MatrixType E(2,2);
    E[0][0] = 5; E[0][1] = 6;
    E[1][0] = 3; E[1][1] = 6;
  BOOST_CHECK_EQUAL(E,set.get_B());
}

BOOST_AUTO_TEST_CASE(test_size){
  SetType::VectorType v(2);
  v[0] = SetType::ScalarType(-1,1); v[1] = SetType::ScalarType(1,3);
  SetType S(v);
  BOOST_CHECK_EQUAL(2, S.size().leftBound());
  BOOST_CHECK_EQUAL(v, SetType::VectorType(S));
}

BOOST_AUTO_TEST_CASE(test_constructors){
  SetType::VectorType v(2), x(2);
  x[0] = 1; x[1] = 0;
  v[0] = SetType::ScalarType(-1,1); v[1] = SetType::ScalarType(-1,3);
  SetType S(x,v);
  SetType::MatrixType C(2,2);
  C[0][0]= 0; C[0][1]= 1;
  C[1][0]= -1; C[1][1]= 0;
  SetType S2(x, C, v);
  v[0] = SetType::ScalarType(0,2);
  BOOST_CHECK_EQUAL(v, SetType::VectorType(S));
  v[0] = SetType::ScalarType(0,4); v[1] = SetType::ScalarType(-1,1);
  BOOST_CHECK_EQUAL(v, SetType::VectorType(S2));

}




#endif /* AFFINESETCOMMONTEST_CPP_ */
