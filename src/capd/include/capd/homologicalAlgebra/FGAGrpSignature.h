/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FGAGrpSignature.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_FGAGRPSIGNATURE_H_)
#define _FGAGRPSIGNATURE_H_

#include <vector>
#include <sstream>
#include <string>
#include "capd/auxil/stringOstream.h"

/* ------------------------  ------------------------ */
  inline std::string fieldStringForm(int){
    return "Z";
  }

/* ------------------------  ------------------------ */
template<typename P_Scalar>
class FGAGrpSignature{
  int m_rank;
  std::vector<int> m_torsionCoef;
  typedef P_Scalar ScalarType;
public:

  FGAGrpSignature(int A_rank=0):m_rank(A_rank){}
  FGAGrpSignature(int A_rank, std::vector<int>& A_torsionCoef):m_rank(A_rank){
    m_torsionCoef=A_torsionCoef;
  }

  int rank() const{return m_rank;}
  int numberOfTorsionCoefs() const{return m_torsionCoef.size();}
  int torsionCoef(int i) const{ return m_torsionCoef[i];}
  bool isTrivial(){
    return rank() == 0 and numberOfTorsionCoefs() == 0;
  }
  FGAGrpSignature& operator+=(const FGAGrpSignature& fga2){
    m_rank+=fga2.m_rank;
    m_torsionCoef.insert(m_torsionCoef.end(),fga2.m_torsionCoef.begin(),fga2.m_torsionCoef.end());
    return *this;
  }
  std::string stringForm(const std::string& R) const{
    std::string s;
    bool plusNeeded=true;
    if(m_rank==1){
      s << R;
    }else if(m_rank){
      s << R << "^" << m_rank;
    }else{
      plusNeeded=false;
      if(m_torsionCoef.size()==0){
        s << "0";
      }
    }

    if(m_torsionCoef.size()>0){
      for(int i=0;i<(int)m_torsionCoef.size();++i){
        if(i>0 || plusNeeded) s << " + ";
        s << R << "/" << m_torsionCoef[i];
      }
    }
    return s;
  }
  std::string getStringForm(const std::string& R) const{
    return stringForm(R);
  }
  friend std::ostream& operator<<(std::ostream& out, const FGAGrpSignature& fga){
    out << fga.getStringForm(fieldStringForm(ScalarType(0)));
    return out;
  }
};


#endif //_FGAGRPSIGNATURE_H_
/// @}

