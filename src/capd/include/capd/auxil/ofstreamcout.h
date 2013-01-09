/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ofstreamcout.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_AUXIL_OFSTREAMCOUT_H_ 
#define _CAPD_AUXIL_OFSTREAMCOUT_H_ 
#include <iostream>
#include <fstream>
class ofstreamcout : public std::ofstream{
  bool streaming;
  public:

  friend ofstreamcout& operator<<(ofstreamcout& out, std::ostream& (*op)(std::ostream&) ){
    if(&out and out.streaming){
      (*op)(std::cout);
      if(!out.bad()) (*op)(out);
    }
    return out;
  }
  template<typename T>
  friend ofstreamcout& operator<<(ofstreamcout& out, const T& t){
    if(&out and out.streaming){
      if(!out.bad()) static_cast<std::ofstream&>(out) << t;
      std::cout << t;
    }
    return out;
  }
  void turnOn(){
    streaming=true;
  }
  void turnOff(){
    streaming=false;
  }
};
#endif // _CAPD_AUXIL_OFSTREAMCOUT_H_ 
/// @}

