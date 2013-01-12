/////////////////////////////////////////////////////////////////////////////
/// @file statistics.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_STATISTICS_H_)
#define _STATISTICS_H_

#include <iterator>
#include <functional>
#include <algorithm>
#include <numeric>
#include <vector>
#include <cmath>

/// @addtogroup basicalg
/// @{

template<class Iterator>
typename std::iterator_traits<Iterator>::value_type average(Iterator beg,Iterator end){
  typename std::iterator_traits<Iterator>::value_type result(0);
  result=std::accumulate(beg,end,result);
  return result/std::distance(beg,end);
}

template<typename Scalar>
std::pair<Scalar,Scalar> linearRegression(const std::vector<Scalar>& x,const std::vector<Scalar>& y){
  Scalar xAv=average(x.begin(),x.end());
  Scalar yAv=average(y.begin(),y.end());
  std::vector<Scalar> xBal(x);
  std::vector<Scalar> yBal(y);
  std::transform(xBal.begin(),xBal.end(),xBal.begin(),std::bind2nd(std::minus<Scalar>(),xAv));
  std::transform(yBal.begin(),yBal.end(),yBal.begin(),std::bind2nd(std::minus<Scalar>(),yAv));

  std::pair<Scalar,Scalar> result;
  Scalar s1(0),s2(0);
  result.first=std::inner_product(xBal.begin(),xBal.end(),yBal.begin(),s1)/
               std::inner_product(xBal.begin(),xBal.end(),xBal.begin(),s2);
  result.second=yAv-result.first*xAv;
  return result;
}

template<typename Scalar>
std::pair<Scalar,Scalar> powerRegression(const std::vector<Scalar>& x,const std::vector<Scalar>& y){
  std::vector<Scalar> xLog(x);
  std::vector<Scalar> yLog(y);
  std::transform(xLog.begin(),xLog.end(),xLog.begin(),std::ptr_fun<Scalar,Scalar>(std::log));
  std::transform(yLog.begin(),yLog.end(),yLog.begin(),std::ptr_fun<Scalar,Scalar>(std::log));
  std::pair<Scalar,Scalar> result=linearRegression<Scalar>(xLog,yLog);
  result.second=std::exp(result.second);
  return result;
}
/// @}
#endif //_STATISTICS_H_

