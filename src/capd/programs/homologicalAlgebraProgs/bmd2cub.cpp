/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file bmd2cub.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 



#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <stdexcept>
#include <new>
using namespace std;

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"

extern ofstreamcout fcout;

#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/bitSet/EuclBitSet.hpp"
#include "capd/auxil/handleUnexpectedTerminate.h"


typedef unsigned long int word;

ofstreamcout fcout;

int main(int argc,char **argv){
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);

  // Check arguments
  if (argc < 3) {
    std::cout << "Usage: " << argv[0] << " inputFile outputFile " << std::endl;
    std::cout << "       inputFile - a text file in bmd format to be converted" << std::endl;
    std::cout << "       outputFile - the resulting text file (cub or fcub extension recommended)" << std::endl;
    exit(0);
  }

  // Open files
  fstream cubfile(argv[2],ios::out);

  if(!cubfile.good()){
    std::cout << "Unable to open CUB file " << argv[2] << " for writing " << std::endl;
    exit(0);
  }

  try{
    BCubSet& cubSet = *new BCubSet(256);
    cubSet.readBmp(argv[1]);
    cubfile << cubSet;
  }catch(std::exception& e){
    cout << "Caught exception: " << e.what() << endl;
  }catch(std::string& s){
    cout << "Caught exception: " << s.c_str() << endl;
  }catch(const char* c){
    cout << "Caught exception: " << c << endl;
  }catch(...){
    cout << "Caught an unknown exception: " << endl;
  }
}

/// @}

