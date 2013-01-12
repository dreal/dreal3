/*
 * FactorReorganization.cpp
 *
 *  Created on: Oct 17, 2009
 *      Author: kapela
 */

#include "capd/capdlib.h"
//#include "capd/dynset/Rect2Set2.hpp"
#include "capd/dynset/C0Rect2Set.hpp"
#include "capd/dynset/FactorReorganization.h"
#include "capd/dynset/CoordWiseReorganization.h"
#include "capd/dynset/ReorganizedSet.h"
using namespace capd;
typedef capd::dynset::C0Rect2Set<IMatrix> BaseSet;
typedef capd::dynset::ReorganizedSet<BaseSet, capd::dynset::CoordWiseReorganization<BaseSet> >  SetType;


#define FIXTURE_NAME CoordReorganize
/*
class FIXTURE_NAME: public ::testing::Test {
protected:

public:
  FIXTURE_NAME(){
  }

  virtual ~FIXTURE_NAME() {
  }
  virtual void SetUp() {

  }
  virtual void TearDown() {
  }
};
*/
#include "AffineSetCommonTest.hpp"
#include "DoubletonSetSpecific.hpp"

BOOST_AUTO_TEST_CASE(test_reorganize) {
  typedef SetType::ScalarType Interval;
  SetType::VectorType x(2), r0(2), r(2);
  x[0] = Interval(-1,3.); x[1] = Interval(2,8);
  SetType set = SetType(x);
  SetType::MatrixType C(2,2);
  C(1,1)= 0; C(1,2)= 2;
  C(2,1)= 2; C(2,2)= 0;
  set.set_C(C);
  r[0] = Interval(-1.,1); r[1]= Interval(-90,100);
  set.set_r(r);
  set.reorganize();
  r0[0] = Interval(-94,104); r0[1] = Interval(-3,3);
  r[0] = Interval(-1,1); r[1] = Interval(0);
  C(1,1)= 0; C(1,2)= 2;
  C(2,1)= 1; C(2,2)= 0;

  BOOST_CHECK_EQUAL(r0, set.get_r0());
  BOOST_CHECK_EQUAL(r,set.get_r());
  BOOST_CHECK_EQUAL(C,set.get_C());
  set.reorganize();
  r0[0] = Interval(-94,104); r0[1] = Interval(-7,7);
  r[0] = Interval(0); r[1] = Interval(0);
  C(1,1)= 0; C(1,2)= 1;
  C(2,1)= 1; C(2,2)= 0;
  BOOST_CHECK_EQUAL(r0, set.get_r0());
  BOOST_CHECK_EQUAL(r,set.get_r());
  BOOST_CHECK_EQUAL(C,set.get_C());

}

BOOST_AUTO_TEST_CASE(test_reorganize2) {
  typedef SetType::ScalarType Interval;
  SetType::VectorType x(2), r0(2), r(2);
  x[0] = Interval(-1,3.); x[1] = Interval(2,8); // (1,5) +[-2,2]x[-3,3]
  SetType set = SetType(x);
  SetType::MatrixType C(2,2);
  C(1,1)= 2; C(1,2)= 2;
  C(2,1)= 2; C(2,2)= 0;
  set.set_C(C);
  r[0] = Interval(-1.,4); r[1]= Interval(-50,100);
  set.set_r(r);
  // r[1] is big so it should replace r0[0]
  set.reorganize();
  r0[0] = Interval(-54,104); r0[1] = Interval(-5,5);
  r[0] = Interval(-1,4); r[1] = Interval(0);
  C(1,1)= 0; C(1,2)= 2;
  C(2,1)= 1; C(2,2)= 0;

  BOOST_CHECK_EQUAL(r0, set.get_r0());
  BOOST_CHECK_EQUAL(r,set.get_r());
  BOOST_CHECK_EQUAL(C,set.get_C());

  set.reorganize();
  r0[0] = Interval(-54,104); r0[1] = Interval(-11,14);
  r[0] = Interval(0); r[1] = Interval(0);
  C(1,1)= 0; C(1,2)= 1;
  C(2,1)= 1; C(2,2)= 0;
  BOOST_CHECK_EQUAL(r0, set.get_r0());
  BOOST_CHECK_EQUAL(r,set.get_r());
  BOOST_CHECK_EQUAL(C,set.get_C());

}

BOOST_AUTO_TEST_CASE(test_findBiggestCoord){
  SetType::VectorType v(4);
  v[0] = 1; v[1] = 2; v[2] = 3; v[3] = 4;
  BOOST_CHECK_EQUAL(3,SetType::findBiggestCoord(v));
  v[0] = 5;
  BOOST_CHECK_EQUAL(0,SetType::findBiggestCoord(v));
}
