/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DynSysMap.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef  _CAPD_DYNSYS_DYNSYSMAP_H_
#define  _CAPD_DYNSYS_DYNSYSMAP_H_
#include "capd/dynsys/DynSys.hpp"

namespace capd{
namespace dynsys{

/**
 *  DynSysMap is a proxy to convert any Map into discrete Dynamical System
 *
 *  This conversion is needed to use Map as dicrete dynamical systems
 *  to move various set representations.  This class implements both
 *  DynSys and C1Map interface.
 *
 *  MapT should be type implementing C1Map interface i.e.
 *  if f is of type MapT then the following expresions should be valid:
 *  f(x) - returns value of a map in x,
 *  f[x] - returns derivative of a map in x
 *  f(x, deriv) returns value of a map and in deriv its derivative.
 */
template <typename MapT>
class DynSysMap : public DynSys<typename MapT::MatrixType>{
public:
	  typedef MapT MapType;
	  typedef typename MapType::MatrixType MatrixType;
	  typedef typename DynSys<MatrixType>::VectorType VectorType;
	  typedef typename DynSys<MatrixType>::ScalarType ScalarType;
	  typedef typename DynSys<MatrixType>::NormType NormType;

	  ///  map should implement C1Map concept
    DynSysMap(const MapType & map) : pMap(&map){
    }

    /// value of a map for a point iv
	  VectorType Phi(const VectorType &iv){
		return (*pMap)(iv);
	  }
	  /// value of a map for a point iv
	  VectorType operator()(const VectorType &iv){
	  	return (*pMap)(iv);
	  }

	  /// derivative of a map in a point iv
	  MatrixType JacPhi(const VectorType &iv){
		  return (*pMap)[iv];
	  }
	  /// derivative of a map in a point iv
	  MatrixType operator[](const VectorType &iv){
	  		  return (*pMap)[iv];
	  }
	  /// value and derivative of a map in a point iv
	  VectorType operator()(const VectorType &iv, MatrixType & derivative){
	  	  	return (*pMap)(iv, derivative);
	  }
	  /// it computes image of the set (in give representation) using set.move function
	  template <typename SetType>
	  SetType & operator()(SetType & set) {
		    set.move(*this);
	        return set;
	  }

	  VectorType & operator()(VectorType &iv) {
	        return (*pMap)(iv);
	  }
	  /// because we have explicit formula for a map not only numerical method
	  /// the remainder term is equal to zero
	  VectorType Remainder(const VectorType &iv){
		  VectorType zero(iv.dimension());
		  return zero;
	  }
	  /// empty implemented - throws exception on use
	  ScalarType Lipschitz(const VectorType &iv, NormType &n){
		  throw "DynSysMap::Lipschitz should not be used!";
		  return ScalarType(0.0);
	  }
	  /// returns name of the class (for backward compatibility)
	  virtual std::string type(void){
	    return "DynSysMap";
	  }
	  virtual ~DynSysMap(){}
protected:
	const MapType * pMap;
};

/// Makes DynSysMap object from given map.
/// Template parameters are recognized automatically.
template <typename MapType>
DynSysMap<MapType> makeDynSysMap(const MapType & map){
	return DynSysMap<MapType>(map);
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_DYNSYSMAP_H_

/// @}

