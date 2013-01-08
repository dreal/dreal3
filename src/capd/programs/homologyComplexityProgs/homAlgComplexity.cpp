/// @addtogroup 2
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file homAlgComplexity.cpp
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
#include <new>
using namespace std;

#include "capd/vectalg/MatrixSlice.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"

extern ofstreamcout fcout;

#include "capd/auxil/statistics.h"

using namespace capd;
using namespace matrixAlgorithms;
using namespace std;


#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubFile.hpp"
#include "capd/homologicalAlgebra/readCubCellSet.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"

typedef unsigned long int cluster;

#include "capd/homologyComplexity/complexityTester.hpp"
#include "capd/homologyComplexity/ObjectGenerators.h"
#include "capd/auxil/handleUnexpectedTerminate.h"
#include "capd/auxil/commandLineArgs.h"
#include "capd/multiEngHom/MultiEngHomT.h"
#include "capd/bitSet/EmbDimException.h"

std::ofstream results;             // for results


template<int dim>
class HomAlgComplexity{
  private:
    int from,to,step;
    std::string inFile,alg,testType;
  public:
    HomAlgComplexity(
      int A_from, int A_to, int A_step,
      std::string A_inFile,std::string A_alg,std::string A_testType
    ): from(A_from),to(A_to),step(A_step),
       inFile(A_inFile),alg(A_alg),testType(A_testType)
    {}
    void operator()(){
      typedef BitSetT<BitmapT<cluster> > BitSet;
      typedef EuclBitSetT<BitSet,dim> EuclBitSet;
      typedef CubSetT<EuclBitSet> BCubSet;
      typedef CubCellSetT<EuclBitSet> BCubCelSet;
      typedef CRef<BCubSet> BCubSetCR;
      typedef CRef<BCubCelSet> BCubCelSetCR;
      typedef CRef<HomologySignature<int> > (*HomologyAlgorithm)(CRef<BCubSet>);
      typedef CRef<HomologySignature<int> > (*HomologyCelAlgorithm)(CRef<BCubCelSet>);
      std::string testDescription=testType;
      CRef<ObjectGenerator<BCubSet> > objectGeneratorCR;
      CRef<ObjectGenerator<BCubCelSet> > objectGeneratorCelCR;

      CRef<BCubCelSet> bCubCelSetCR;
      if(testType == "scaled" ||
         testType == "scaledD2" ||
         testType == "scaledCel" ||
         testType == "scaledD2Cel" ||
         testType == "shifted"
      ){
        try{
          bCubCelSetCR=readCubCellSet<BCubSet,BCubCelSet>(inFile.c_str());
        }catch(std::runtime_error){
          throw EmbDimException("Incorrect embDim");
        }catch(EmbDimException){
          throw EmbDimException("Incorrect embDim");
        }
        fcout << "Original enclosing box is ";
        for(int i=0;i<bCubCelSetCR().embDim();++i){
          fcout << bCubCelSetCR().getUnpaddedWidth(i) << " ";
        }
        fcout  << std::endl;
      }

      if(testType == "scaled"){
        objectGeneratorCR=CRef<ObjectGenerator<BCubSet> >(new RescaledObjectGenerator<BCubCelSet,BCubSet>(bCubCelSetCR));
      }else if(testType == "scaledD2"){
        objectGeneratorCR=CRef<ObjectGenerator<BCubSet> >(new RescaledD2ObjectGenerator<BCubCelSet,BCubSet>(bCubCelSetCR));
      }else if(testType == "scaledCel"){
        objectGeneratorCelCR=CRef<ObjectGenerator<BCubCelSet> >(new RescaledObjectGenerator<BCubCelSet,BCubCelSet>(bCubCelSetCR));
      }else if(testType == "scaledD2Cel"){
        objectGeneratorCelCR=CRef<ObjectGenerator<BCubCelSet> >(new RescaledD2ObjectGenerator<BCubCelSet,BCubCelSet>(bCubCelSetCR));
      }else if(testType == "shifted"){
        objectGeneratorCR=CRef<ObjectGenerator<BCubSet> >(new ShiftedObjectGenerator<BCubCelSet,BCubSet>(bCubCelSetCR));
      }else if(testType == "subset"){
        CRef<BCubSet> bCubSetCR=readCubFile<BCubSet,BCubCelSet>(inFile.c_str());
        objectGeneratorCR=CRef<ObjectGenerator<BCubSet> >(new SubObjectGenerator<BCubSet,BCubSet>(bCubSetCR));
      }else if(testType == "linSubset"){
        CRef<BCubSet> bCubSetCR=readCubFile<BCubSet,BCubCelSet>(inFile.c_str());
        objectGeneratorCR=CRef<ObjectGenerator<BCubSet> >(new LinearSubObjectGenerator<BCubSet,BCubSet>(bCubSetCR));
      }else if(testType == "linSubsetCel"){
        CRef<BCubCelSet> bCubCellSetCR=readCubCellSet<BCubCelSet,BCubCelSet>(inFile.c_str());
        objectGeneratorCelCR=CRef<ObjectGenerator<BCubCelSet> >(new LinearSubObjectGenerator<BCubCelSet,BCubCelSet>(bCubCellSetCR));
      }else if(testType == "masked"){
        CRef<BCubSet> bCubSetCR=readCubFile<BCubSet,BCubCelSet>(inFile.c_str());
        objectGeneratorCR=CRef<ObjectGenerator<BCubSet> >(new MaskedObjectGenerator<BCubSet,BCubSet>(bCubSetCR));
      }else{
        fcout << "Test type " << testType << " Unknown\n";
        exit(1);
      }

      if(testType == "scaledCel" || testType == "scaledD2Cel" || testType == "linSubsetCel"){
        HomologyCelAlgorithm selectedAlgorithm=MultiEngineHomology<dim>::selector.setupHomologyCelAlgorithm(alg);
        ComplexityTester<ObjectGenerator<BCubCelSet>,HomologySignature<int> > tester(
          *objectGeneratorCelCR,
          selectedAlgorithm,
          testDescription
        );
        std::string s=tester.findComplexity(from,to,step,fcout);
        fcout << s;
        results << s;
      }else{
        HomologyAlgorithm selectedAlgorithm=MultiEngineHomology<dim>::selector.setupHomologyAlgorithm(alg);
        ComplexityTester<ObjectGenerator<BCubSet>,HomologySignature<int> > tester(
          *objectGeneratorCR,
          selectedAlgorithm,
          testDescription
        );
        std::string s=tester.findComplexity(from,to,step,fcout);
        fcout << s;
        results << s;
      }
    }
};

int main(int argc,char** argv){
  try{
    set_unexpected(handle_unexpected);
    set_terminate(handle_terminate);
    fcout.open("details.out");
    results.open("summary.out");
    fcout.turnOn();
    readAcyclicConfigs();

    setupCommandLineArgs;
    declareCommandLineArg(int,from,1);
    declareCommandLineArg(int,to,from);
    declareCommandLineArg(int,step,1);
    declareCommandLineArg(std::string,inFile,"");
    declareCommandLineArg(std::string,alg,"MM_CR");
    declareCommandLineArg(std::string,testType,"scaled");
    declareCommandLineArg(std::string,help,"");
    if(!to) to=from;
    std::string executableName("homAlgComplexity");

    if((inFile=="" && help=="") || help=="1"){
      help="intro";
    }

    if(help != ""){
      if(help=="intro"){
        fcout << "\n --- This is " << executableName << "  --- \n\n";
        fcout << "\n Author: M. Mrozek\n\n";
        fcout << "\n With homology software by W. Kalies,  M. Mrozek and P. Pilarczyk\n\n";
        fcout << "Usage: \n\n";
        fcout << "      " << executableName << " inFile=filename\n\n";
        fcout << "Type: \n\n";
        fcout << "      " << executableName << " help=options\n\n";
        fcout << "to learn more \n";
        exit(0);
      }else if(help=="options"){
        fcout << "\n --- This is " << executableName << "  --- \n\n";
        fcout << "To learn about available options type: \n\n";
        fcout << "      " << executableName << " help=xx\n\n";
        fcout << "where xx may be: \n\n";
        fcout << "tests - available tests\n";
        fcout << "algorithms - available algorithms\n";
        fcout << "input   - available input formats \n";
        exit(0);
      }else if(help=="algorithms"){
        fcout << "\n --- This is " << executableName << "  --- \n\n";
        fcout << "To select a particular homology algorithm implementation add option: \n\n";
        fcout << " alg=xx\n\n";
        fcout << "where xx denotes one of the available homology algorithms implementations: \n";
        fcout << "   BK\n";
        fcout << "     - written by Bill Kalies <wkalies@fau.edu> \n";
        fcout << "   BK_bm or BK_LT\n";
        fcout << "     - written by Bill Kalies with preprocessing by Marcio Gameiro \n";
        fcout << "   MM_CR, MM_AS, MM_ASLT, MM_ASR, MM_ASH or MM_AR\n";
        fcout << "     - written by Marian Mrozek <Marian.Mrozek@ii.uj.edu.pl>\n";
        fcout << "   PP or PP_AS\n";
        fcout << "     - written by Pawel Pilarczyk <http://www.PawelPilarczyk.com/>\n";
        fcout << "You may add ns to the names of some implementations\n";
        fcout << "to prevent them from preprocessing the homology computations with shaving\n";
        exit(0);
      }else if(help=="input"){
        fcout << "\n --- This is " << executableName << "  --- \n\n";
        fcout << "" << executableName << " accepts files in the following formats\n";
        fcout << "   bmp - two dimensional bitmaps in the standard BMP bitmap format\n";
        fcout << "   bmd - multidimensional bitmaps in the bmd format\n";
        fcout << "   cub/txt - various text formats\n";
        fcout << "Consult http://chomp.rutgers.edu/ for details\n";
        fcout << "or see the enclosed examples\n";
        exit(0);
      }else if(help=="tests"){
        fcout << "\n --- This is " << executableName << "  --- \n\n";
        fcout << "To select a particular test use option\n\n";
        fcout << " testType=test  \n\n";
        fcout << "The main tests are  \n";
        fcout << "  scaled - for rescaled full cubical sets  \n";
        fcout << "  scaledCel - for rescaled general cubical sets  \n";
        fcout << "  linSubset - for subsets of full cubical sets  \n";
        fcout << "  linSubsetCel - for subsets of general cubical sets  \n";
        fcout << "The options controlling tests are  \n\n";
        fcout << "   from=m to=n step=k\n\n";
        fcout << "where \n";
        fcout << "   m - initial size\n";
        fcout << "   n - final sizeg\n";
        fcout << "   k - step by which rescallings/subsets are increased\n";
        exit(0);
      }
    }
    MultiEngineHomology<0> meh; // Needed to initialize engines!
    HomAlgComplexity<2> hac2(from,to,step,inFile,alg,testType);
    HomAlgComplexity<3> hac3(from,to,step,inFile,alg,testType);
    HomAlgComplexity<4> hac4(from,to,step,inFile,alg,testType);
    HomAlgComplexity<5> hac5(from,to,step,inFile,alg,testType);
    HomAlgComplexity<6> hac6(from,to,step,inFile,alg,testType);
    HomAlgComplexity<7> hac7(from,to,step,inFile,alg,testType);
    HomAlgComplexity<8> hac8(from,to,step,inFile,alg,testType);

    for(int i=8;i>=2;--i){   // reversed order of search to override problems with 2 dim bitmap (should be tested last)
      try{
        switch(i){
          case 2: hac2();
                  goto done;
          case 3: hac3();
                  goto done;
          case 4: hac4();
                  goto done;
          case 5: hac5();
                  goto done;
          case 6: hac6();
                  goto done;
          case 7: hac7();
                  goto done;
          case 8: hac8();
                  goto done;
          default:;
        }
      }catch(EmbDimException& e ){
      }
    }
    std::cout << "The selected engine and/or dimension is incorrect.\nThis executable supports only dimensions 2,3,4,5,6,7 and 8" << std::endl;
    done:;
  }catch(std::exception& e){
    fcout << "Caught exception: " << e.what() << endl;
  }catch(std::string& s){
    fcout << "Caught exception: " << s.c_str() << endl;
  }catch(const char* c){
    fcout << "Caught exception: " << c << endl;
  }catch(...){
    fcout << "Caught an unknown exception: " << endl;
  }
}
/// @}

