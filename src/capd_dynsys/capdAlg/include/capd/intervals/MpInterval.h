/////////////////////////////////////////////////////////////////////////////
/// @file MpInterval.h
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifdef __HAVE_MPFR__

#ifndef _CAPD_INTERVAL_MPINTERVAL_H_ 
#define _CAPD_INTERVAL_MPINTERVAL_H_ 

#include "capd/intervals/Interval.hpp"
#include "capd/intervals/IntervalTraits.h"
#include "capd/multiPrec/MpReal.h"
namespace capd{
namespace intervals{

typedef capd::multiPrec::MpReal MpReal;
typedef capd::multiPrec::MpReal MpfrClass;
typedef Interval<MpReal, MpReal> MpInterval;

template <>
class IntervalIOTraits<MpReal>{
public:
	typedef MpReal BoundType;
	static std::ostream & bitWrite(std::ostream & out, const BoundType & x){
		throw std::runtime_error(" bitWrite not implemented for given type!");
		return out;
	}
	static std::istream & bitRead(std::istream & in, BoundType & x){
		throw std::runtime_error(" bitRead not implemented for given type!");
		return in;
	}
	static std::ostream & hexWrite(std::ostream & out, const BoundType & x){
		throw std::runtime_error(" hexWrite not implemented for given type!");
		return out;
	}
	static std::istream & hexRead(std::istream & in, BoundType & x){
		throw std::runtime_error(" hexRead not implemented for given type!");
		return in;
	}
	static BoundType readDown(const std::string & in){
		 BoundType r;
		 r.get(in, MpReal::RoundDown);
		 return r;
	}
	static BoundType readUp(const std::string & in){
		 BoundType r;
		 r.get(in, MpReal::RoundUp);
		 return r;
	}
};


}}

#include "capd/intervals/MpInterval_Fun.hpp"

#endif // _CAPD_INTERVAL_MPINTERVAL_H_

#endif


