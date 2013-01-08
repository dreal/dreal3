/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file HomologySignature.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_HOMOLOGYSIGNATURE_H_)
#define _HOMOLOGYSIGNATURE_H_
#include <vector>
#include <sstream>
#include <string>

#include "capd/homologicalAlgebra/FGAGrpSignature.h"

template<typename ScalarType>
class HomologySignature : public std::vector<FGAGrpSignature<ScalarType> >{
  public:

  HomologySignature(){}
  HomologySignature(std::vector<FGAGrpSignature<ScalarType> >& A_FGAGrSignVect){
    *(std::vector<FGAGrpSignature<ScalarType> >*)(this)=A_FGAGrSignVect;
  }
  HomologySignature(std::vector<int>& A_Betti){
    for(int i=0;i<(int)A_Betti.size();++i) this->push_back(FGAGrpSignature<ScalarType> (A_Betti[i]));
  }
  int topDim() const { return this->size()-1;}

  HomologySignature& operator+=(const HomologySignature& hs2){
    unsigned int i=0;
    for(i=0;i<this->size();++i){
      if(i<hs2.size()) (*this)[i]+=hs2[i];
    }
    for(;i<hs2.size();++i){
      push_back(hs2[i]);
    }
    return *this;
  }

  friend std::ostream& operator<<(std::ostream& out, const HomologySignature& fga){
    if(fga.topDim()<0){
      out << "  0" << std::endl;
    }else{
      for(int i=0;i<(int)fga.size();++i){
        out << "  H_" << i << " = " << fga[i] << std::endl;
      }
    }
    return out;
  }

  void shrink(){
    if(this->empty()) return;
    typename std::vector<FGAGrpSignature<ScalarType> >::iterator it=this->end();
    while((--it)>=this->begin() and it->isTrivial()) erase(it);
  }

  int bettiNumber(int i){
    if(i>=0 and i<=topDim()) return (*this)[i].rank();
    else return 0;
  }

  std::string bettiVector() const{
    std::ostringstream o;
    for(unsigned int i=0;i<this->size();++i){
      if(i) o << ",";
      o << (*this)[i].rank();
    }
    return o.str();
  }
};
#endif //_HOMOLOGYSIGNATURE_H_
/// @}

