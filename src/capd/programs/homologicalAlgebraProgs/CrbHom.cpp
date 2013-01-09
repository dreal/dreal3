/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrbHom.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/*
    This is the version of the CrHom.cpp file adapted to compute
    not only Betti and torsion numbers but also the homology basis
*/



#include "capd/homologicalAlgebra/CrbHomology.hpp"

void handle_unexpected() {
  fcout << "unexpected exception thrown" << std::endl;
  exit(0);
}

void handle_terminate() {
  fcout << "terminate() called" << std::endl;
  exit(0);
}

ofstreamcout fcout;

int main(int argc,char **argv){
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);
  try{

    fcout.open("out.txt");
    fcout.turnOn();

    // Check arguments
    if (argc < 2) {
      std::cout << "!Usage " << argv[0] << " filename " << std::endl;
      exit(0);
    }

    CrbHom(argv[1]);
  }catch(std::exception& e){
    fcout << "Caught exception: " << e.what() << endl;
  }catch(std::string& s){
    fcout << "Caught exception: " << s.c_str() << endl;
  }catch(const char* c){
    fcout << "Caught exception: " << c << endl;
  }catch(...){
    fcout << "Caught an unknown exception: " << endl;
  }
}

/// @}

