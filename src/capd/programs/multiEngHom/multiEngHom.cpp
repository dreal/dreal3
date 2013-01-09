/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file multiEngHom.cpp
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

#include "capd/multiEngHom/MultiEngHomT.h"
#include "capd/auxil/handleUnexpectedTerminate.h"
#include "capd/auxil/commandLineArgs.h"


int main(int argc,char** argv){
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);
  fcout.open("chomp_raport.txt");
  fcout.turnOn();

  setupCommandLineArgs;
  declareCommandLineArg(std::string,inFile,"");
  declareCommandLineArg(std::string,engine,"MM_CR");
  declareCommandLineArg(std::string,help,"");
  declareCommandLineArg(int,verbose,1);
  std::string executableName("ChomP");
  std::string version(" ver. 1.01");

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
    if(inFile=="help") help="options";
  }


  if(help != ""){
    if(help=="intro"){
      fcout << "\n --- This is " << executableName+version << "  --- \n\n";
      fcout << "Basic usage: \n\n";
      fcout << "      " << executableName << " filename\n\n";
      fcout << "Type: \n\n";
      fcout << "      " << executableName << " help=options\n\n";
      fcout << "to learn about available engines, file formats and other options \n";
      exit(0);
    }else if(help=="options"){
      fcout << "\n --- This is " << executableName+version << "  --- \n\n";
      fcout << "To learn about available options type: \n\n";
      fcout << "      " << executableName << " help=xx\n\n";
      fcout << "where xx may be: \n\n";
      fcout << "engines - available engines\n";
      fcout << "input   - available input formats \n";
      fcout << "output  - available output formats \n";
      exit(0);
    }else if(help=="engines"){
      fcout << "\n --- This is " << executableName+version << "  --- \n\n";
      fcout << "" << executableName << " has several engines for computing Betti numbers. \n";
      fcout << "In some situations some engines may work faster than the preselected one. \n";
      fcout << "To specify a concrete engine use option: \n\n";
      fcout << " engine=xx\n\n";
      fcout << "where xx denotes one of the available engines: \n";
      fcout << "   BK or BK_LT\n";
      fcout << "     - engines written by Bill Kalies <wkalies@fau.edu>\n";
      fcout << "   MM_CR, MM_ASLT or MM_AR\n";
      fcout << "     - engines written by Marian Mrozek <Marian.Mrozek@ii.uj.edu.pl>\n";
      fcout << "   PP or PP_AS\n";
      fcout << "     - engines written by Pawel Pilarczyk <http://www.PawelPilarczyk.com/>\n";
      fcout << "Consult http://chomp.rutgers.edu/ for details\n";
      exit(0);
    }else if(help=="input"){
      fcout << "\n --- This is " << executableName+version << "  --- \n\n";
      fcout << "" << executableName << " accepts files in the following formats\n";
      fcout << "   bmp - two dimensional bitmaps in the standard BMP bitmap format\n";
      fcout << "   bmd - multidimensional bitmaps in the bmd format\n";
      fcout << "   cub/txt - various text formats\n";
      fcout << "Consult http://www.math.gatech.edu/~chomp/ for details\n";
      exit(0);
    }else if(help=="output"){
      fcout << "\n --- This is " << executableName+version << "  --- \n\n";
      fcout << "The amount of information provided may be controlled with  \n\n";
      fcout << "   verbose=n\n\n";
      fcout << "where n means the following output\n";
      fcout << "   0 - only Betti numbers\n";
      fcout << "   1 - Betti numbers and computation time (default)\n";
      fcout << "   2 - Betti and torsion numbers\n";
      fcout << "   3 - Betti and torsion numbers with some details of the computation process\n";
      fcout << "Consult http://www.math.gatech.edu/~chomp/ for details\n";
      exit(0);
    }
  }

  try{
    MultiEngineHomology<0> ch;
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

