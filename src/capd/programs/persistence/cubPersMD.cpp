/// @addtogroup persistence
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file cubPersistenceMD.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (c) Marian  Mrozek, Krakow 2007-2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

/**********************************************************/
/****************** cubPersistenceMD.cpp ******************/
/******** (c) Marian  Mrozek, Krakow 2007-2010 ************/
/**********************************************************/

#include "capd/homologicalAlgebra/InclusionHomology.hpp"
#include "capd/auxil/commandLineArgs.h"
#include "capd/auxil/stringOstream.h"
#include "capd/auxil/CRef.h"
#include "capd/persistence/PersistenceMatrix.hpp"
#include "capd/persistence/FilteredCubset.hpp"
#include <cstdlib>
#include <iomanip>

//#define _USE_KRAK_
#ifdef _USE_KRAK_
  #include "capd/krak/krak.h"
  #include "capd/krak/color.h"
  #include "capd/krak/noframe.h"
  Frame intervalsFrame;
#endif

/* ------------------------  ------------------------ */
void handle_unexpected() {
  std::cout << "unexpected exception thrown" << std::endl;
  exit(0);
}

/* ------------------------  ------------------------ */
void handle_terminate() {
  std::cout << "terminate() called" << std::endl;
  exit(0);
}

/* ------------------------  ------------------------ */

ofstreamcout fcout;
float fx0,fy0,fz0,fx1,fy1,fz1;  // for debugging only: in principle shoud be 0 and 1

// ******************************************************** //
int main(int argc,char **argv){
  typedef ECellMDCodeT<cluster,2> CubFaceIndexD2Type;
  typedef ReductionPairT<CubFaceIndexD2Type> ReductorD2Type;
  typedef ECellMDCodeT<cluster,3> CubFaceIndexD3Type;
  typedef ReductionPairT<CubFaceIndexD3Type> ReductorD3Type;

  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);
  #ifdef _USE_KRAK_
    openGW(1024,768,WHITE,BLACK,20,20);
    intervalsFrame.initFrm(10,10,1004,718,WHITE,BLACK);
  #endif
  std::string baseName;

  setupCommandLineArgs;
  declareCommandLineArg(std::string,inFile,"");
  declareCommandLineArg(std::string,task,"all");
  declareCommandLineArg(std::string,help,"");
  declareCommandLineArg(std::string,name,"");
  declareCommandLineArg(int,botLevel,1);
  declareCommandLineArg(int,topLevel,0);
  declareCommandLineArg(bool,shave,true);
  declareCommandLineArg(bool,storeMatrices,true);
  declareCommandLineArg(bool,simplify,true);
  declareCommandLineArg(int,embDim,0);
  declareCommandLineArg(float,bx,0); fx0=bx;
  declareCommandLineArg(float,by,0); fy0=by;
  declareCommandLineArg(float,bz,0); fz0=bz;
  declareCommandLineArg(float,cx,1); fx1=cx;
  declareCommandLineArg(float,cy,1); fy1=cy;
  declareCommandLineArg(float,cz,1); fz1=cz;

/*
  // If there is only one switch with no value (i.e. the default value 1)
  // we take it as the name of the input file
  std::pair<int,std::string> vc= getValueCountAndArg(std::string("1"));
  if(vc.first==1){
    inFile=vc.second;
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

  baseName << inFile << ".";
  if(name !="") baseName=name+"."+baseName;
  std::string outFname=baseName+"out.txt";

  fcout.turnOn();
  fcout.open(outFname.c_str());

  string executableName="cubPersMD";
  string s = executableName;
  s << " Ver. 0.99 (c) Marian Mrozek, " << __DATE__ << " " << __TIME__ << "\n";
  fcout << s;

  if(argc < 2 || (inFile=="")){
    fcout << "Basic usage: " <<executableName << " filename\n";
    exit(0);
  };

  FilteredCubset<ReductorD2Type,int,2> filtCubset2(baseName);
  FilteredCubset<ReductorD3Type,int,3> filtCubset3(baseName);

  Stopwatch sw;
  try{
    int minLevelFound=0;
    int nLevels=0;
    int dim=0;
    if(task == "all" || task == "inclusions"){
      for(int d=2;d<=3;++d){
        try{
          switch(d){
            case 2: minLevelFound=filtCubset2.readData(inFile);
                    dim=2;
                    nLevels=filtCubset2.nLevels;
                    goto dataRead;
            case 3: minLevelFound=filtCubset3.readData(inFile);
                    dim=3;
                    nLevels=filtCubset3.nLevels;
                    goto dataRead;
          }
        }catch(int){}
      }
      dataRead:
      if(dim==0) throw "This executable is compiled for dimensions 2 or 3";
    }
    if(task == "intervals" && !embDim){
      throw("Use option embDim=number to provide the embedding dimension!");
      dim=embDim;
    }
    if(!topLevel) topLevel=nLevels;
    if(minLevelFound>botLevel) botLevel=minLevelFound;

    switch(dim){
      case 2: filtCubset2.process(task,botLevel,topLevel,shave,storeMatrices,simplify); break;
      case 3: filtCubset3.process(task,botLevel,topLevel,shave,storeMatrices,simplify); break;
      default: throw("This executable supports only embedding dimensions 2 and 3!");
    }
  }catch(std::exception& e){
    std::cout << "Caught exception: " << e.what() << endl;
    #ifdef _USE_KRAK_
      rootFrame << At(20,20) << "Caught exception: " << e.what();
    #endif
  }catch(std::string& s){
    std::cout << "Caught exception: " << s.c_str() << endl;
    #ifdef _USE_KRAK_
      rootFrame << At(20,20) << "Caught exception: " << s.c_str();
    #endif
  }catch(const char* c){
    std::cout << "Caught exception: " << c << endl;
    #ifdef _USE_KRAK_
      rootFrame << At(20,20) << "Caught exception: " <<c;
    #endif
  }catch(...){
    std::cout << "Caught an unknown exception: " << endl;
    #ifdef _USE_KRAK_
      rootFrame << At(20,20) << "Caught an unknown exception";
    #endif
  }
  #ifdef _USE_KRAK_
    waitBt();
    closeGW();
  #endif
  fcout << "Total computation time is " << sw  << std::endl;
  fcout << "===== Done =====\n";
  return 0;
}

/// @}

