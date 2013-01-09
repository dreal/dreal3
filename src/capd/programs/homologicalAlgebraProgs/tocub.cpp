/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file RedHom.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.




#include "capd/homologicalAlgebra/toCub.hpp"
#include "capd/auxil/commandLineArgs.h"
#include "capd/auxil/handleUnexpectedTerminate.h"
#include "capd/homologicalAlgebra/acyclicConfigs.hpp"

ofstreamcout fcout;

int main(int argc,char **argv){

  Stopwatch swTot;
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);
  fcout.open("report.txt");
  fcout.turnOn();

/*
  setupCommandLineArgs;
  declareCommandLineArg(std::string,inFile,"");
  declareCommandLineArg(std::string,engine,"AR");
  declareCommandLineArg(std::string,help,"");
  declareCommandLineArg(int,mod,0);
  declareCommandLineArg(int,verbose,0);

  std::string version(" 0.99 ");
  std::string copyright("(C) M. Mrozek, CAPD Group, 2010");
  std::string logo(executableName+version+copyright);
  std::string webpage("http://redhom.ii.uj.edu.pl");

//showCommandLineArgs;
  fcout << logo  << std::endl;

  int fileCount=getCommandLineFileCount();
  if(fileCount!=2){
    throw "Two file names are needed";
  }else if(fileCount==0 && help==""){
    help="intro";
  }else{
    inFile=getCommandLineFile(1);
    if(inFile=="help") help="intro";
  }
*/

  std::string executableName("tocub");

  if (argc < 2) {
      std::cout << executableName << " converts cubical set from binary to text format. Usage\n";
      std::cout << "      " << executableName << " fileName\n";
      std::cout << "or\n";
      std::cout << "      " << executableName << " inpFileName.ext outFileName.ext\n";
    exit(0);
  }
  std::string inName,outName;
  if (argc < 3) {
    inName=std::string(argv[1])+".bmd";
    outName=std::string(argv[1])+".cub";
  }else{
    inName=std::string(argv[1]);
    outName=std::string(argv[2]);
  }

  try{
    toCub(inName.c_str(),outName.c_str());
  }catch(std::exception& e){
    std::cout << "Caught exception: " << e.what() << endl;
  }catch(std::string& s){
    std::cout << "Caught exception: " << s.c_str() << endl;
  }catch(const char* c){
    std::cout << "Caught exception: " << c << endl;
  }catch(...){
    std::cout << "Caught an unknown exception: " << endl;
  }
  std::cout << "Total time (including input/output) " << swTot  << std::endl;

}

/// @}

