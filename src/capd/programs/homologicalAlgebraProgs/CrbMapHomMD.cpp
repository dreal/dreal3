/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrbMapHomMD.cpp
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

#include "capd/homologicalAlgebra/CrbMapHomMD.h"
#include "capd/auxil/handleUnexpectedTerminate.h"
#include "capd/auxil/commandLineArgs.h"

int main(int argc,char** argv){
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);
  fcout.open("report.txt");
  fcout.turnOn();

  setupCommandLineArgs;
  declareCommandLineArg(std::string,inFile,"");
  declareCommandLineArg(std::string,help,"");
  declareCommandLineArg(int,verbose,2);
  declareCommandLineArg(bool,preshave,true);
  std::string executableName("CrbMapHomMD");
  std::string version(" 0.95 ");
  std::string copyright("(c) Marian Mrozek, 2010");
  std::string logo(executableName+version+copyright);

  //showCommandLineArgs;

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
      std::cout << logo  << std::endl;
      std::cout << "Basic usage: \n";
      std::cout << "      " << executableName << " filename\n";
/*
      std::cout << "Type: \n";
      std::cout << "      " << executableName << " help=xx\n";
      std::cout << "where xx may be:  engines, input  or output\n";
      std::cout << "to learn about available engines and input/output formats\n";
*/
      exit(0);
/*
    }else if(help=="engines"){
      std::cout << logo  << std::endl;
      std::cout << "" << executableName << " has two basic engines for computing Betti numbers. \n";
      std::cout << "To specify a concrete engine use the option: \n\n";
      std::cout << " engine=xx\n\n";
      std::cout << "where xx may be AS, ASR, ASH, ASLT \n";
      std::cout << "Consult http://ii.uj.edu.pl/~mrozek/software/homology.html for details\n";
      exit(0);
    }else if(help=="input"){
      std::cout << logo  << std::endl;
      std::cout << "" << executableName << " accepts files in the following formats\n";
      std::cout << "   bmp - two dimensional bitmaps in the standard BMP bitmap format\n";
      std::cout << "   bmd - multidimensional bitmaps in the bmd format\n";
      std::cout << "   cub/txt - various text formats\n";
      std::cout << "Consult http://ii.uj.edu.pl/~mrozek/software/homology.html for details\n";
      exit(0);
    }else if(help=="output"){
      std::cout << logo  << std::endl;
      std::cout << "The amount of information provided may be controlled with  \n\n";
      std::cout << "   verbose=n\n\n";
      std::cout << "where n means the following output\n";
      std::cout << "   0 - only Betti numbers\n";
      std::cout << "   1 - Betti numbers and computation time (default)\n";
      std::cout << "   2 - Betti and torsion numbers\n";
      std::cout << "   3 - Betti and torsion numbers with some details of the computation process\n";
      std::cout << "Consult http://ii.uj.edu.pl/~mrozek/software/homology.html for details\n";
      exit(0);
*/
    }
  }

  try{
    std::cout << logo  << std::endl;
    CrbMapHom<0> ch;
    ch(inFile.c_str(),preshave,verbose);
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

