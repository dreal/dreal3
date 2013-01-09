/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file AsHomMD.cpp
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
#include <sstream>
#include <exception>
#include <new>
using namespace std;

#include "capd/homologicalAlgebra/AsHomMD.h"
#include "capd/auxil/handleUnexpectedTerminate.h"
#include "capd/auxil/commandLineArgs.h"

int main(int argc,char** argv){
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);
  fcout.open("report.txt");
  fcout.turnOn();

  setupCommandLineArgs;
  declareCommandLineArg(std::string,inFile,"");
  declareCommandLineArg(std::string,engine,"AS");
  declareCommandLineArg(std::string,help,"");
  declareCommandLineArg(int,verbose,2);
  std::string executableName("AsHomMD");
  std::string version(" 0.95 ");
  std::string copyright("(c) Marian Mrozek, 2006-2007");
  std::string logo(executableName+version+copyright);

/*
  std::pair<int,std::string> vc= getValueCountAndArg(std::string("1"));
  if(vc.first>1){
    fcout << "Only one file can be processed\n";
    exit(1);
  }else if(vc.first==1){
    if(vc.second=="help") help="options";
    else inFile=vc.second;
  }else if(vc.first==0 && help==""){
    help="intro";
  }
*/
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
      fcout << "where xx may be:  engines, input  or output\n";
      fcout << "to learn about available engines and input/output formats\n";
      exit(0);
    }else if(help=="engines"){
      fcout << logo  << std::endl;
      fcout << "" << executableName << " has two basic engines for computing Betti numbers. \n";
      fcout << "To specify a concrete engine use the option: \n\n";
      fcout << " engine=xx\n\n";
      fcout << "where xx may be AS, ASR, ASH, ASLT \n";
      fcout << "Consult http://ii.uj.edu.pl/~mrozek/software/homology.html for details\n";
      exit(0);
    }else if(help=="input"){
      fcout << logo  << std::endl;
      fcout << "" << executableName << " accepts files in the following formats\n";
      fcout << "   bmp - two dimensional bitmaps in the standard BMP bitmap format\n";
      fcout << "   bmd - multidimensional bitmaps in the bmd format\n";
      fcout << "   cub/txt - various text formats\n";
      fcout << "Consult http://ii.uj.edu.pl/~mrozek/software/homology.html for details\n";
      exit(0);
    }else if(help=="output"){
      fcout << logo  << std::endl;
      fcout << "The amount of information provided may be controlled with  \n\n";
      fcout << "   verbose=n\n\n";
      fcout << "where n means the following output\n";
      fcout << "   0 - only Betti numbers\n";
      fcout << "   1 - Betti numbers and computation time (default)\n";
      fcout << "   2 - Betti and torsion numbers\n";
      fcout << "   3 - Betti and torsion numbers with some details of the computation process\n";
      fcout << "Consult http://ii.uj.edu.pl/~mrozek/software/homology.html for details\n";
      exit(0);
    }
  }

  try{
    AsHom<0> ch;
    ch(inFile.c_str(),engine,verbose);
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

