/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file setAcyclicConfigsD3.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2005-2006 by Marian Mrozek
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <iostream>
#include <fstream>
#include <vector>
#include <map>
#include "capd/auxil/ofstreamcout.h"
ofstreamcout fcout;

#include "capd/homologicalAlgebra/acyclicConfigs.hpp"

//typedef unsigned long int cluster;
//  static const int dim=4;
//  static const int dim=3;
#include "capd/auxil/handleUnexpectedTerminate.h"
#include "capd/auxil/commandLineArgs.h"


bool acyclicConfigsD3Embedded(const unsigned char *c){
  for(int i=0;i<100;++i){
    if(acyclicConfigsD3[i] != *(c+i)) return false;
  }
  return true;
}

int main(int argc,char** argv){
  try{
    fcout.open("details.txt");
    fcout.turnOn();
    using namespace std;
    ifstream executable(argv[1],std::ios::binary);

    if(argc < 2){
      fcout << "Usage: setAcyclicConfigsD3 executableName";
      exit(0);
    }
    if (!executable.good()){
      fcout << "Unable to open " << argv[1] <<endl ;
      exit(0);
    }

    executable.seekg(0);
    unsigned int b=executable.tellg();
    executable.seekg(0,std::ios::end);
    unsigned int e=executable.tellg();
    int length=e-b;

    std::vector<unsigned char> data(length);
    executable.seekg(0);
    fcout << "Length is " << length << std::endl;
    executable.read((char*)(&data[0]),length);
    executable.close();

    readAcyclicConfigs();
    fcout << "Reading ... " << std::endl;
    for(unsigned char* c=&data[0];c<&data[length-100];++c){
      if(acyclicConfigsD3Embedded(c)){
        fcout << "acyclicConfigsD3 table already imported" << std::endl;
        return 0;
      }
      if(0==strcmp((char*)c,ACYCLIC_CONFIGS_D3MARKER)){
        fcout << "Marker found" << std::endl;
        for(unsigned char* d=&acyclicConfigsD3[0];d<&acyclicConfigsD3[acyclicConfigsSize];++d) *(c++)=*d;
        ofstream executable(argv[1],std::ios::binary);
        executable.write((char*)(&data[0]),length);
        fcout << "acyclicConfigsD3 table successfuly imported" << std::endl;
        return 0;
      }
    }

    fcout << "acyclicConfigsD3: Failure - Marker not found!" << std::endl;
    exit(0);
  }catch(std::exception& e){
    fcout << "Caught exception: " << e.what() << std::endl;
  }catch(std::string& s){
    fcout << "Caught exception: " << s.c_str() << std::endl;
  }catch(const char* c){
    fcout << "Caught exception: " << c << std::endl;
  }catch(...){
    fcout << "Caught an unknown exception: " << std::endl;
  }

}

/// @}

