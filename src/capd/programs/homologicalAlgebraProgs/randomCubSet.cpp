/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file randomCubSet.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2005-2008 by Marian Mrozek
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <new>
using namespace std;

#include "capd/bitSet/randomCubSet.h"
#include "capd/auxil/handleUnexpectedTerminate.h"
#include "capd/auxil/commandLineArgs.h"

int main(int argc,char** argv){
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);
  fcout.open("report.txt");
  fcout.turnOn();

  setupCommandLineArgs;
  declareCommandLineArg(std::string,outFile,"cubcellset.bmd");
  declareCommandLineArg(int,embdim,3);
  declareCommandLineArg(int,size,128);
  declareCommandLineArg(int,seed,0);
  declareCommandLineArg(double,frequency,0.5);
  std::string executableName("randomCubSet");
  std::string version(" 0.9 ");
  std::string copyright("(c) Marian Mrozek, 2008");
  std::string logo(executableName+version+copyright);


  try{
    randomStart(seed);
    generate(outFile.c_str(),embdim,size,frequency);
  }catch(std::exception& e){
    fcout.turnOn();
    fcout << "Caught exception: " << e.what() << endl;
  }catch(std::string& s){
    fcout.turnOn();
    fcout << "Caught exception: " << s.c_str() << endl;
  }catch(const char* c){
    fcout.turnOn();
    fcout << "Caught exception: " << c << endl;
  }catch(...){
    fcout.turnOn();
    fcout << "Caught an unknown exception: " << endl;
  }

}

/// @}

