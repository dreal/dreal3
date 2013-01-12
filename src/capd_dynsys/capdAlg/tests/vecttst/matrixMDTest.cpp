/// @addtogroup vecttst
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file matrixMDTest.cpp
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
#include <stdexcept>
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/Matrix.h"

using namespace capd::vectalg;

int main(int argc, char* argv[]){
  try{
    Matrix<double,0,0> m(1,1);
    std::istringstream s("{{5.0,4.5,4.0},{3.5,3.0,2.5},{-7.0 , 5, -8 }}");
    s >> m;
    std::cout << "m=" << m << std::endl;

    double data[]={
          1.0, 2.0, 3.0, 4.0,
          0.0, 1.0, 2.0, 3.0,
          0.0, 0.0, 1.0, 2.0
       };
    Matrix<double,0,0> A(3,4,data);
    std::cout << "A=" << A << std::endl;
    Matrix<double,0,0> B(4,3);
    B=Transpose(A);
    std::cout << "B=A^T=" << B << std::endl;
    Matrix<double,0,0> C(3,3);
    C=A*B;
    std::cout << "C=A*B=" <<  C << std::endl;
    Vector<double,0> v(1,2,3);
    std::cout << "C*"  << v << "=" << C*v << std::endl;
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
