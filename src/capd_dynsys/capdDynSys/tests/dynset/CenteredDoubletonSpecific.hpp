// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CenteredDoubletonSecific.hpp
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_CENTEREDDOUBLETONSECiFIC_HPP_
#define _CAPD_CENTEREDDOUBLETONSECiFIC_HPP_
BOOST_AUTO_TEST_CASE(test_constructor_x_r0){
  SetType::VectorType x(2);
  x[0] = SetType::ScalarType(-1,1); x[1] = SetType::ScalarType(-2,-2);
  SetType::VectorType r0(2);
  r0[0] = SetType::ScalarType(-3,3); r0[1] = SetType::ScalarType(1,3);

  SetType T(x,r0);
  x[0] = 0.; x[1] = 0;
  BOOST_CHECK_EQUAL(x,T.get_x());
  r0[0]= SetType::ScalarType(-4,4);
  r0[1]= SetType::ScalarType(-1,1);
  BOOST_CHECK_EQUAL(r0,T.get_r0());
}

#endif // _CAPD_CENTEREDDOUBLETONSECiFIC_HPP_

/// @}
