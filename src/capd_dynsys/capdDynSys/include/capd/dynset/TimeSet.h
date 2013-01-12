/////////////////////////////////////////////////////////////////////////////
/// @file TimeSet.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.


#ifndef _CAPD_DYNSET_TIMESET_H_
#define _CAPD_DYNSET_TIMESET_H_

#include <sstream>
#include "capd/dynsys/NonAutDynSys.h"
#include "capd/vectalg/Norm.hpp"

namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

///////////////////////////////////////////////////////////////////////////////////
/// TimeSet is a class for computing trajectories of an nonautononous ODE.
/// The base class is an arbitrary class of C^0-C^r set
///
//////////////////////////////////////////////////////////////////////////////////
template<typename BaseSetT>
class TimeSet : public BaseSetT{
public:
  typedef typename BaseSetT::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef BaseSetT BaseSet;

  TimeSet(BaseSet& baseSet, const ScalarType& currentTime) 
    : BaseSet(baseSet), m_currentTime(currentTime) 
  {}

  ~TimeSet(){}

  using BaseSet::size;

  template<class Solver>
  void move(capd::dynsys::NonAutDynSys<Solver>& dynsys)
  {
    dynsys.setCurrentTime(m_currentTime);
    BaseSet::move(dynsys);
    m_currentTime += dynsys.getStep();
  }

  template<class Solver>
  void move(capd::dynsys::NonAutDynSys<Solver>& dynsys, TimeSet& result){
    dynsys.setCurrentTime(m_currentTime);
    BaseSet::move(dynsys,dynamic_cast<BaseSet&>(result));
    result.m_currentTime += dynsys.getStep();
  }


  std::string show(void) const{
    std::ostringstream out;
    out << BaseSet::show();
    out << "\ntime: "<< m_currentTime << "\n";
    return out.str();
  }

  const ScalarType& getCurrentTime() const
  {
    return m_currentTime;
  }

  TimeSet &operator=(const VectorType &v){
    BaseSet::operator=(v);
    return *this;
  }

  TimeSet &operator=(const TimeSet &S){
    BaseSet::operator=(S);
    m_currentTime = S.m_currentTime;
    return *this;
  }

protected:
  ScalarType m_currentTime;

};

/// @}
}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_TIMESET_H_
