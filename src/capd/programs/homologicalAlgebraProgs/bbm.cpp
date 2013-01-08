/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file bbm.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#include "capd/homologicalAlgebra/bbm.hpp"
#include "capd/auxil/commandLineArgs.h"

#include "capd/auxil/handleUnexpectedTerminate.h"

ofstreamcout fcout;




int main(int argc,char **argv){
  Stopwatch swTot;
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);
  fcout.open("report.txt");
  fcout.turnOn();

  setupCommandLineArgs;
  declareCommandLineArg(std::string,inFile,"");
  declareCommandLineArg(std::string,engine,"AR");
  declareCommandLineArg(std::string,help,"");
  declareCommandLineArg(int,verbose,2);
  std::string executableName("bbm");
  std::string version(" 0.91 ");
  std::string copyright("(c) Marian Mrozek, 2010");
  std::string logo(executableName+version+copyright);

  int fileCount=getCommandLineFileCount();
  if(fileCount>1){
    throw "Only one file can be processed";
  }else if(fileCount==0 && help==""){
    help="intro";
  }else{
    inFile=getCommandLineFile(1);
    if(inFile=="help") help="intro";
  }

  if(help != ""){
    if(help=="intro"){
      fcout << logo  << std::endl;
      fcout << "Basic usage: \n";
      fcout << "      " << executableName << " filename\n";
      fcout << "Type: \n";
      fcout << "      " << executableName << " help=xx\n";
      fcout << "where xx may be:  input  or output\n";
      fcout << "to learn about available input/output formats\n";
      exit(0);
    }else if(help=="input"){
      fcout << logo  << std::endl;
      fcout << "" << executableName << " accepts files in the following formats\n";
//      fcout << "   bmp - two dimensional bitmaps in the standard BMP bitmap format\n";
//      fcout << "   bmd - multidimensional bitmaps in the bmd format\n";
      fcout << "   cub/txt - various text formats\n";
      fcout << "Consult http://ii.uj.edu.pl/~mrozek/software/homology.html for details\n";
      exit(0);
    }else if(help=="output"){
      fcout << logo  << std::endl;
      fcout << "The amount of information provided may be controlled with  \n\n";
      fcout << "   verbose=n\n\n";
      fcout << "where n means the following output\n";
      fcout << "   0 - only Betti numbers\n";
      fcout << "   1 - Betti numbers and computation time \n";
      fcout << "   2 - Betti and torsion numbers (default)\n";
      fcout << "   3 - Betti and torsion numbers with some details of the computation process\n";
      fcout << "Consult http://ii.uj.edu.pl/~mrozek/software/homology.html for details\n";
      exit(0);
    }
  }


  fcout.open("out.txt");
  fcout.turnOn();
  try{
    fcout << logo  << std::endl;
    bbmMD(inFile.c_str());
  }catch(std::exception& e){
    fcout << "Caught exception: " << e.what() << endl;
  }catch(std::string& s){
    fcout << "Caught exception: " << s.c_str() << endl;
  }catch(const char* c){
    fcout << "Caught exception: " << c << endl;
  }catch(...){
    fcout << "Caught an unknown exception: " << endl;
  }
  std::cout << "Total time (including input/output) " << swTot  << std::endl;
}

/// @}

