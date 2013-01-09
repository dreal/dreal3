/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file cub2bmd.cpp
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
    std::cout << "       inputFile - a text file in cub format to be converted" << std::endl;
    std::cout << "       outputFile - the resulting binary file (bmd extension recommended)" << std::endl;
    exit(0);
  }

  // Open files
  fstream cubfile(argv[1],ios::in);

  if(!cubfile.good()){
    std::cout << "Unable to open CUB file " << argv[1] << " for reading " << std::endl;
    exit(0);
  }

  try{
    BCubSet& cubSet = *new BCubSet(256);
    cubfile >> cubSet;
    unsigned int multidimType='D'*256+'B'; // for multidimensional full cubical sets
    cubSet.writeBmp(argv[2],multidimType);
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

