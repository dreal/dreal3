//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file CnMapTests.hpp
///
/// @author Tomasz Kapela   @date 2010-02-27
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _UNITTESTS_MAP_CNMAPTESTS_HPP_
#define _UNITTESTS_MAP_CNMAPTESTS_HPP_

#include "capd/capdlib.h"
#include "capd/map/CnMap.hpp"

#define BOOST_TEST_MODULE ICnMapTest
#include <boost/test/included/unit_test.hpp>
#include <boost/test/floating_point_comparison.hpp>

//typedef capd::ICnMap MapType;
typedef capd::map::CnMap<capd::IMatrix, 4> MapType;
typedef MapType::VectorType VectorType;
typedef MapType::ScalarType ScalarType;
typedef MapType::CnCoeffType CnCoeffType;


std::vector<double> computeAtanDer(MapType::VectorType & x){
  double v = x[0].leftBound();
  std::vector<double> result;
  result.push_back(atan(v));
  result.push_back(1/(1+v*v));
  result.push_back(-2*v/(sqr(1+v*v)));
  return result;
}


template <typename DVectorT, typename IVectorT>
inline void compareResults(const DVectorT & expected, const IVectorT & result, const std::string & msg, double tolerance = 1.0e-12)
{
  typename IVectorT::const_iterator it = result.begin();
  typename DVectorT::const_iterator ex = expected.begin();
  for(int i=0; ex != expected.end(); ++ex, ++i, ++it){
    BOOST_CHECK_MESSAGE(subset(*ex,*it), msg << "  derivative : " << i );
    BOOST_CHECK_CLOSE(*ex, it->rightBound(), tolerance);
  }
}

BOOST_AUTO_TEST_CASE(xatan)
{
  std::string txt = "var:x;fun:atan(x);",
              msg = "Function \"" + txt + "\"  x = " ;
  MapType f(txt,4);
  VectorType x(1);
  x[0] = 1.0;
  std::vector<double> expected = computeAtanDer(x);
  CnCoeffType df(1, 3);
//  std::cout << "\n dim f = " << f.dimension() << "  \n dim df = " << df.dimension();
  f.computeDerivatives(x,df);
//  std::cout << "\ndf = " << df.toString();
  compareResults(expected, df, msg+"1.0");

  MapType g("var:x;fun:-atan(-x);",4);
  g.computeDerivatives(x,df);
  compareResults(expected, df, msg+"1.0");

  x[0] = 3.0;
  expected = computeAtanDer(x);
//  x[0] = 2.0;
  f.computeDerivatives(x,df);
  compareResults(expected, df, msg+"3.0");

  x[0] = 0.0;
  expected = computeAtanDer(x);
  f.computeDerivatives(x,df);
  compareResults(expected, df, msg+"0.0");

}


#endif // _UNITTESTS_MAP_CNMAPTESTS_HPP_

