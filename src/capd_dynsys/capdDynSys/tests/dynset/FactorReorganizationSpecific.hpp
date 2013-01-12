// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FactorReorganization.cpp
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef __FACTOR_REORGANIZATION_SPECIFIC_HPP_
#define __FACTOR_REORGANIZATION_SPECIFIC_HPP_

BOOST_AUTO_TEST_CASE(test_reorganize) {
  typedef SetType::ScalarType Interval;
  SetType::VectorType x(2), r0(2), r(2);
  x[0] = Interval(-1,3.); x[1] = Interval(2,8);
  SetType set = SetType(x);
  SetType::MatrixType C(2,2);
  C(1,1)= 0; C(1,2)= 3;
  C(2,1)= 2; C(2,2)= 0;
  set.set_C(C);
  r[0] = Interval(-1.,1); r[1]= Interval(-90.,100.);
  set.set_r(r);
  BOOST_CHECK(set.isReorganizationNeeded());
  set.reorganize();
  r0[0] = Interval(-10,10); r0[1] = Interval(-94.,104.);
  r[0] = Interval(0.,0.); r[1] = Interval(0.);
  C(1,1)= 1; C(1,2)= 0;
  C(2,1)= 0; C(2,2)= 1;

  BOOST_CHECK_EQUAL(r0, set.get_r0());
  BOOST_CHECK_EQUAL(r,set.get_r());
  BOOST_CHECK_EQUAL(C,set.get_C());
  // set.setFactor(1);
  BOOST_CHECK_EQUAL(1.0,set.getFactor());
  BOOST_CHECK(!set.isReorganizationNeeded());

  set.reorganize();
  BOOST_CHECK_EQUAL(r0, set.get_r0());
  BOOST_CHECK_EQUAL(r,set.get_r());
  BOOST_CHECK_EQUAL(C,set.get_C());
}

BOOST_AUTO_TEST_CASE(test_reorganize2) {
  typedef SetType::ScalarType Interval;
  SetType::VectorType x(2), r0(2), r(2);
  x[0] = Interval(-1,3.); x[1] = Interval(2.,8.); // (1,5) +[-2,2]x[-3,3]
  SetType set = SetType(x);
  SetType::MatrixType C(2,2);
  C(1,1)= 2; C(1,2)= 2;
  C(2,1)= 2; C(2,2)= 0;
  set.set_C(C);
  r[0] = Interval(-1.,4.); r[1]= Interval(-50.,100.);
  set.set_r(r);

  set.reorganize();
  r0[0] = Interval(-11,14); r0[1] = Interval(-54.,104.);
  r[0] = Interval(0); r[1] = Interval(0.);
  C(1,1)= 1; C(1,2)= 0;
  C(2,1)= 0; C(2,2)= 1;

  BOOST_CHECK_EQUAL(r0, set.get_r0());
  BOOST_CHECK_EQUAL(r,set.get_r());
  BOOST_CHECK_EQUAL(C,set.get_C());
}

#endif //__FACTOR_REORGANIZATION_SPECIFIC_HPP_
/// @}
