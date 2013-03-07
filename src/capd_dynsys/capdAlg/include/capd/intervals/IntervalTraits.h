//////////////////////////////////////////////////////////////////////////////
///
///  @file IntervalTraits.h
///  
///  @author kapela  @date   Sep 5, 2011
//////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2011 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INTERVALS_INTERVALTRAITS_H_
#define _CAPD_INTERVALS_INTERVALTRAITS_H_
#include <iostream>
#include "capd/basicalg/ieeePrimitive.h"

namespace capd {
namespace intervals {
/// @addtogroup intervals
/// @{


template <typename T_Bound>
class IntervalTraits{
public:
  typedef T_Bound BoundType;
  typedef BoundType BoundContainer;
  typedef const BoundType &  BoundReturnType;
  typedef BoundType & BoundRefType;
};

template <>
class IntervalTraits<double>{
public:
  typedef double BoundType;
  typedef volatile BoundType BoundContainer;
  typedef BoundType BoundReturnType;
  typedef BoundType & BoundRefType;
};

template <>
class IntervalTraits<float>{
public:
  typedef float BoundType;
  typedef volatile BoundType BoundContainer;
  typedef BoundType BoundReturnType;
  typedef BoundType & BoundRefType;
};

template <>
class IntervalTraits<long double>{
public:
  typedef long double BoundType;
  typedef volatile BoundType BoundContainer;
  typedef BoundType BoundReturnType;
  typedef BoundType & BoundRefType;
};

template <typename T_Bound>
class IntervalIOTraits{
public:
	typedef T_Bound BoundType;
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
		throw std::runtime_error(" readDown not implemented for given type!");
	}
	static BoundType readUp(const std::string & in){
		throw std::runtime_error(" readUp not implemented for given type!");
	}
};

template <>
class IntervalIOTraits<double>{
public:
	typedef double BoundType;
	static std::ostream & bitWrite(std::ostream & out, const BoundType & x){
		capd::basicalg::Primitive::basicBitImage(x, out);
		return out;
	}
	static std::istream & bitRead(std::istream & in, BoundType & x){
		x = capd::basicalg::constructFromBitSet<BoundType>(in);
		return in;
	}
	static std::ostream & hexWrite(std::ostream & out, const BoundType & x){
		capd::basicalg::Primitive::basicHexImage(x, out);
		return out;
	}
	static std::istream & hexRead(std::istream & in, BoundType & x){
		x = capd::basicalg::constructFromHexSet<BoundType>(in);
		return in;
	}
	static BoundType readDown(const std::string & in){
		return capd::basicalg::inferFromString<BoundType,false>(in);
	}
	static BoundType readUp(const std::string & in){
		return capd::basicalg::inferFromString<BoundType,true>(in);
	}
};

template <>
class IntervalIOTraits<float>{
public:
public:
	typedef float BoundType;
	static std::ostream & bitWrite(std::ostream & out, const BoundType & x){
		capd::basicalg::Primitive::basicBitImage(x, out);
		return out;
	}
	static std::istream & bitRead(std::istream & in, BoundType & x){
		x = capd::basicalg::constructFromBitSet<BoundType>(in);
		return in;
	}
	static std::ostream & hexWrite(std::ostream & out, const BoundType & x){
		capd::basicalg::Primitive::basicHexImage(x, out);
		return out;
	}
	static std::istream & hexRead(std::istream & in, BoundType & x){
		x = capd::basicalg::constructFromHexSet<BoundType>(in);
		return in;
	}
	static BoundType readDown(const std::string & in){
		return capd::basicalg::inferFromString<BoundType,false>(in);
	}
	static BoundType readUp(const std::string & in){
		return capd::basicalg::inferFromString<BoundType,true>(in);
	}
};


/// @} 
}} // end of namespace capd::intervals

#endif /* _CAPD_INTERVALS_INTERVALTRAITS_H_ */
