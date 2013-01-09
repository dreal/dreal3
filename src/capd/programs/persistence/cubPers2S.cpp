/// @addtogroup persistence
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file cubPersistence2S.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (c) Marian  Mrozek, Krakow 2007-2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

/**********************************************************/
/****************** cubPersistence2S.cpp ******************/
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
  std::string leftBaseName,rightBaseName;

  setupCommandLineArgs;
  declareCommandLineArg(std::string,leftFile,"");
  declareCommandLineArg(std::string,rightFile,"");
  declareCommandLineArg(std::string,task,"all");
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

  if(leftFile == "" || rightFile == "") throw("Left or right file name missing!");

  leftBaseName << leftFile << ".";
  if(name !="") leftBaseName=name+"."+leftBaseName;
//  std::string leftOutFname=leftBaseName+"out.txt";
  rightBaseName << rightFile << ".";
  if(name !="") rightBaseName=name+"."+rightBaseName;
//  std::string rightOutFname=rightBaseName+"out.txt";

  fcout.turnOn();
  fcout.open("out.txt");

  string executableName="cubPers2S";
  string s = executableName;
  s << " Ver. 0.99 (c) Marian Mrozek, " << __DATE__ << " " << __TIME__ << "\n";
  fcout << s;

  if(argc < 2 ){
    fcout << "Basic usage: " <<executableName << " leftFile=filename1 rightFile=filename2\n";
    exit(0);
  };

  FilteredCubset<ReductorD2Type,int,2> leftFiltCubset2(leftBaseName);
  FilteredCubset<ReductorD2Type,int,2> rightFiltCubset2(rightBaseName);
  FilteredCubset<ReductorD3Type,int,3> leftFiltCubset3(leftBaseName);
  FilteredCubset<ReductorD3Type,int,3> rightFiltCubset3(rightBaseName);

/*
  FilteredCubset<2> leftFiltCubset2(leftBaseName);
  FilteredCubset<2> rightFiltCubset2(rightBaseName);
  FilteredCubset<3> leftFiltCubset3(leftBaseName);
  FilteredCubset<3> rightFiltCubset3(rightBaseName);
*/

  Stopwatch sw;
  try{
    int leftMinLevelFound=0,rightMinLevelFound=0;
    int lefTnLevels=0,righTnLevels=0;
    int dim=0;
    if(task == "all" || task == "inclusions"){
      for(int d=2;d<=3;++d){
        try{
          switch(d){
            case 2: leftMinLevelFound=leftFiltCubset2.readData(leftFile);
                    rightMinLevelFound=rightFiltCubset2.readData(rightFile);
                    lefTnLevels=leftFiltCubset2.nLevels;
                    righTnLevels=rightFiltCubset2.nLevels;
                    dim=2;
                    goto dataRead;
            case 3: leftMinLevelFound=leftFiltCubset3.readData(leftFile);
                    rightMinLevelFound=rightFiltCubset3.readData(rightFile);
                    dim=3;
                    lefTnLevels=leftFiltCubset3.nLevels;
                    righTnLevels=rightFiltCubset3.nLevels;
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
    int leftTopLevel=topLevel,rightTopLevel=topLevel;
    int leftBotLevel=botLevel,rightBotLevel=botLevel;

    if(!leftTopLevel) leftTopLevel=lefTnLevels;
    if(!rightTopLevel) rightTopLevel=righTnLevels;
    if(leftMinLevelFound>leftBotLevel) leftBotLevel=leftMinLevelFound;
    if(rightMinLevelFound>rightBotLevel) rightBotLevel=rightMinLevelFound;

    switch(dim){
      case 2: leftFiltCubset2.process(task,leftBotLevel,leftTopLevel,shave,storeMatrices,simplify);
              rightFiltCubset2.process(task,rightBotLevel,rightTopLevel,shave,storeMatrices,simplify);
              leftFiltCubset2.writeMatchingMatrix(rightFiltCubset2.getTopHomFiltr());
              if(!(leftFiltCubset2.topCubSetCR()==rightFiltCubset2.topCubSetCR())){
                fcout << "Left: " << leftFiltCubset2.topCubSetCR().cardinality() << " cardinality\n";
                fcout << "Right: " << rightFiltCubset2.topCubSetCR().cardinality() << " cardinality\n";
                throw "Final left and right sets do not coincide";
              }
              break;
      case 3: leftFiltCubset3.process(task,leftBotLevel,leftTopLevel,shave,storeMatrices,simplify);
              rightFiltCubset3.process(task,rightBotLevel,rightTopLevel,shave,storeMatrices,simplify);
              leftFiltCubset3.writeMatchingMatrix(rightFiltCubset3.getTopHomFiltr());
              break;
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

