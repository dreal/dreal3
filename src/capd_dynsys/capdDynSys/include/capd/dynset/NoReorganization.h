/////////////////////////////////////////////////////////////////////////////
/// @file NoReorganization.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_NOREORGANIZATION_H_
#define _CAPD_DYNSET_NOREORGANIZATION_H_

namespace capd{
namespace dynset{

///
///  Reorganization that does nothing.
///
template <typename SetT>
class NoReorganization  {

public:
  typedef SetT SetType;
  typedef typename SetType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
 // typedef typename ScalarType::BoundType BoundType;

  NoReorganization(double factor=0.0){}

  void reorganize(SetType & result) const{
  }

  bool isReorganizationNeeded(const SetType & result) const{
    return false;
  }
  bool reorganizeIfNeeded(SetType & result) const{
    return false;
  }
  void setFactor(double factor) {
  }
  double getFactor() const {
    return 0.0;
  }
  void disableSwapping(){
  }
  void disableReorganization(){
  }
  std::string name() const{
      return "no reorganization";
  }
  std::string toString() const {
       return "";
  }
};

}
}

#endif /* _CAPD_DYNSET_NOREORGANIZATION_H_ */
