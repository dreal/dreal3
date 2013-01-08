/// @addtogroup vecttst
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file vectMDTest.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <cassert>
#include <sstream>
#include "capd/vectalg/Vector.h"

using namespace capd::vectalg;

int main(int argc, char* argv[]){
  try{
    Vector<int,0> v(5),w(5),z(1);
    std::istringstream s("{5,3,2},{2},{-7 , 5 }");
    s >> z;
    std::cout << " z=" << z << std::endl;
    s >> z;
    std::cout << " z=" << z << std::endl;
    s >> z;
    std::cout << " z=" << z << std::endl;
    for(int i=0;i<5;++i){
      v[i]=2*i+1;
      w[i]=10-i;
    }
    z=v;
    std::cout << " z=" << z << std::endl;
    std::cout << v+w << std::endl;
  }catch(std::exception& e){
    std::cout << "Exception caught: " << e.what() << std::endl;
  }catch(const char *c){
    std::cout << "Exception caught: " << c << std::endl;
  }catch(...){
    std::cout << "Unknown Exception caught: " << std::endl;
  }
  return 0;
}

/// @}
