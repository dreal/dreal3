/// @addtogroup persistence
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FilteredCubset.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (c) Marian  Mrozek, Krakow 2007-2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _FILTEREDCUBSET_HPP_
#define _FILTEREDCUBSET_HPP_


/* MM */
#include "capd/homologicalAlgebra/InclusionHomology.hpp"
#include "capd/auxil/commandLineArgs.h"
#include "capd/auxil/stringOstream.h"
#include "capd/auxil/CRef.h"
#include "capd/persistence/PersistenceMatrix.hpp"
#include <cstdlib>
#include <iomanip>

//#define _USE_KRAK_
#ifdef _USE_KRAK_
  #include "capd/krak/krak.h"
  #include "capd/krak/color.h"
  #include "capd/krak/noframe.h"
  Frame intervalsFrame;
#endif

extern ofstreamcout fcout;
extern float fx0,fy0,fz0,fx1,fy1,fz1;  // for debugging only: in principle shoud be 0 and 1

const int max2dSize=16000;
const int max3dSize=500;
const int maxEmbDim=3;
const int cxDim=100,cyDim=100,czDim=100; // for debugging only
const int bxDim=0,byDim=0,bzDim=0; // for debugging only
const int maxAdmissibleNumberOfLevels=1000;




//template<int setEmbDim>
template<typename P_Reductor, typename P_Scalar, int setEmbDim>
class FilteredCubset{
  typedef unsigned long int cluster;

  typedef P_Scalar ScalarType;
//  typedef ECellMDCodeT<cluster,setEmbDim,ScalarType> CubFaceIndexType;
  typedef ECellMDCodeT<cluster,setEmbDim> CubFaceIndexType;
  typedef BitSetT<BitmapT<cluster> > BitSet;
  typedef EuclBitSetT<BitSet,setEmbDim> EuclBitSet;
  typedef CubSetT<EuclBitSet> BCubSet;
  typedef CRef<BCubCelSet> BCubCelSetCR;
  typedef CubCellSetT<EuclBitSet,P_Reductor> SCubCelSet;
  typedef capd::vectalg::Matrix<ScalarType,0,0> MatrixType;
  typedef FreeModule<CubFaceIndexType,MatrixType> FreeModuleType;
  typedef FreeChainComplex<FreeModuleType> FreeChainComplexType;
  typedef ChainT<std::map<int,ScalarType> > SparseIntVector;
  typedef std::vector<SparseIntVector> SparseIntMatrix;
  typedef std::vector<SparseIntMatrix> GradedSparseIntMatrix;
  typedef std::vector<CRef<SparseIntMatrix> > FilteredCRefSparseIntMatrix;
  typedef std::vector<FilteredCRefSparseIntMatrix> GradedFilteredCRefSparseIntMatrix;
  typedef std::vector<CRef<SparseIntMatrix> >  GradedCRefSparseIntMatrix;
  typedef capd::vectalg::Matrix<ScalarType,0,0> IntMatrix;
  typedef std::vector<IntMatrix> FilteredIntMatrix;
  typedef std::vector<FilteredIntMatrix> GradedFilteredIntMatrix;

private:
  std::string baseName;
  unsigned short* data;
  int xDim,yDim,zDim;

  std::vector<std::vector<int> > bettiNumbers;
  std::vector<std::vector<std::vector<int> > > persistentBettiNumbers;
  std::vector<std::vector<std::vector<int> > > persistenceIntervals;
  std::vector<int> numberOfIntervals;

  CRef<GradedFilteredIntMatrix> inclusionMatricesCR;
  CRef<CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> > topHomFiltrCR;

  /* ------------------------  ------------------------ */
  inline unsigned int index(int x,int y,int z){
    return x+xDim*(y+yDim*z);
  }
public:
  int nLevels;
  CRef<SCubCelSet> topCubCellSetCR;
  CRef<BCubSet> topCubSetCR;

  FilteredCubset(const std::string& s){
    data=0;
    baseName=s;
    bettiNumbers.reserve(maxAdmissibleNumberOfLevels);
    persistentBettiNumbers.reserve(maxAdmissibleNumberOfLevels);
    persistenceIntervals.reserve(maxAdmissibleNumberOfLevels);
    numberOfIntervals.reserve(setEmbDim);
    for(int i=0;i<maxAdmissibleNumberOfLevels;++i){
      bettiNumbers.push_back(std::vector<int>());
      bettiNumbers[i].reserve(setEmbDim);
      persistentBettiNumbers.push_back(std::vector<std::vector<int> >());
      persistentBettiNumbers[i].reserve(maxAdmissibleNumberOfLevels);
      persistenceIntervals.push_back(std::vector<std::vector<int> >());
      persistenceIntervals[i].reserve(maxAdmissibleNumberOfLevels);
      for(int j=0;j<maxAdmissibleNumberOfLevels;++j){
        persistentBettiNumbers[i].push_back(std::vector<int>());
        persistentBettiNumbers[i][j].reserve(setEmbDim);
        persistenceIntervals[i].push_back(std::vector<int>());
        persistenceIntervals[i][j].reserve(setEmbDim);
      }
    }

  }
  ~FilteredCubset(){
    if(data) delete[] data;
  }

  CRef<CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> > getTopHomFiltr(){
    return topHomFiltrCR;
  }

  int readData(const std::string& inFile){
    ifstream in(inFile.c_str());
    int locDim;
    in >> locDim;
    if(locDim != setEmbDim) throw locDim;
    if(in.fail()){
      string s="File ";
      s << inFile.c_str() << " is empty, inaccessible or does not exist! ";
      throw s;
    }
    if(locDim < 2 || locDim > 3){
      std::string s;
      s << "This executable is compiled for dimensions 2 or 3 and the data file is in dimension " << locDim << "\n";
      throw s;
    }
    if(locDim == 3){
      in >> xDim >> yDim >> zDim;
      if(zDim==1) locDim=2;
    }else if(locDim == 2){
      in >> xDim >> yDim;
      zDim = 1;
    }
    if(locDim == 3){
      if( xDim>max3dSize || yDim>max3dSize || zDim>max3dSize){
        string s="The maximum allowed size in one direction for 3D set is ";
        s << max3dSize;
        throw s;
      }
    }else if(locDim == 2){
      if( xDim>max2dSize || yDim>max2dSize || zDim>max2dSize){
        string s="The maximum allowed size in one direction for 2D set is ";
        s << max2dSize;
        throw s;
      }
    }

    fcout << " Enclosing box is " << xDim;
    if(locDim>=2) fcout << "x" << yDim;
    if(locDim>=3) fcout << "x" << zDim;
    fcout << std::endl;

    int nLevelsLoc=1;
    bool levelZeroFound=false;
    data=new unsigned short[xDim*yDim*zDim];
    if(!data) throw "Not enough memory for data\n";
    int minLevelFound=maxAdmissibleNumberOfLevels;

    for(int k=0;k<zDim;++k)
    for(int j=0;j<yDim;++j)
    for(int i=0;i<xDim;++i){
      int c;
      if(in.eof()) throw std::string("Premature end of file encountered\n");
      in >> c;
      if(c>nLevelsLoc) nLevelsLoc=c;
      if(c>0 && c<minLevelFound) minLevelFound=c;
      if(c==0) levelZeroFound=true;
      if(nLevelsLoc>maxAdmissibleNumberOfLevels){
        std::string s;
        s << "Maximum number of " << maxAdmissibleNumberOfLevels << " levels exceeded\n";
        throw s;
      }
      if(c<0) throw "Level value must be at least zero\n";
      data[index(i,j,k)]=(unsigned short)c;
    }
    fcout << "Found levels from " << minLevelFound << " to " << nLevelsLoc << std::endl;
    if(!levelZeroFound){
      nLevels=nLevelsLoc;
    }else{
      nLevels=nLevelsLoc+1;
      fcout << "Level 0 will be changed to level " << nLevels << std::endl;
      for(int k=0;k<zDim;++k)
      for(int j=0;j<yDim;++j)
      for(int i=0;i<xDim;++i){
        if(data[index(i,j,k)] == 0){
          data[index(i,j,k)] = (unsigned short)nLevels;
        }
      }
    }
    return minLevelFound;
  }
  // ******************************************************** //
  CRef<CubSetT<EuclBitSetT<BitSet,setEmbDim> > > makeBCubSet(int level){
    typedef EuclBitSetT<BitSet,setEmbDim> EuclBitSet;
    typedef CubSetT<EuclBitSet> BCubSet;
    typedef CRef<BCubCelSet> BCubCelSetCR;

    int coordsMin[3];
    int coordsMax[3];

    coordsMin[0]=int(0.5+xDim*fx0);
    coordsMin[1]=int(0.5+yDim*fy0);
    coordsMin[2]=int(0.5+zDim*fz0);
    coordsMax[0]=int(0.5+xDim*fx1);
    coordsMax[1]=int(0.5+yDim*fy1);
    coordsMax[2]=int(0.5+zDim*fz1);

    //fcout << " coordsMin is (" << coordsMin[0] << "," << coordsMin[1] << "," << coordsMin[2] << ")\n";
    //fcout << " coordsMax is (" << coordsMax[0] << "," << coordsMax[1] << "," << coordsMax[2] << ")\n";
    CRef<BCubSet> cubSetCR(new BCubSet(coordsMax));
    cubSetCR().clear();
    int coords[maxEmbDim];
    for(coords[0]=coordsMin[0];coords[0]<coordsMax[0];++coords[0])
    for(coords[1]=coordsMin[1];coords[1]<coordsMax[1];++coords[1])
    for(coords[2]=coordsMin[2];coords[2]<coordsMax[2];++coords[2])
    if( data[index(coords[0],coords[1],coords[2])] <= level ){
      typename BCubSet::BitCoordIterator it(cubSetCR(),&coords[0]);
      it.setBit();
    }
    cubSetCR().addEmptyCollar();
    fcout << "Constructed set in " << coordsMax[0] << "x" << coordsMax[1];
    if(setEmbDim==3) fcout << "x" << coordsMax[2];
    fcout << "\n";
    int card=cubSetCR().cardinality();
    fcout << "Set cardinality: " << card << std::endl;
    string s="Empty set found on level ";
    s << level;
    if(!card) throw s;
    return cubSetCR;
  }

  // ******************************************************** //


  void findInclusionMaps(int botLevel,int topLevel,bool shave,bool storeMatrices){
    inclusionMatricesCR=CRef<GradedFilteredIntMatrix>(new GradedFilteredIntMatrix);
    for(int g=0;g<setEmbDim;++g){
      inclusionMatricesCR().push_back(FilteredIntMatrix());
    }
    BCubSet::neighbAcyclicBI=&BCubSet::neighbAcyclicLT;
    Stopwatch swtot;
    // We begin with generating the cubset for the bottom level
    CRef<BCubSet> subCubSetCR=makeBCubSet(botLevel);

    std::string imatFname=baseName+"imatrices.txt";
    std::ofstream imat;
    if(storeMatrices) imat.open(imatFname.c_str());
    std::string bettiFname=baseName+"betti.txt";
    std::ofstream bettiOut(bettiFname.c_str());

    // shaving may speed up computations
    if(shave){
      BCubSet empty(subCubSetCR());
      empty.clear();
      subCubSetCR().shaveWithFixedSubset(empty);
      fcout << "Shaving reduced the set to " << subCubSetCR().cardinality() << " cubes" << std::endl;
    }

    // full cubical set only needed for shaving. Now we need its decomposition to cells for the coreduction algorithm
    // and the coreduction homology model called here cubcellset filtration
    CRef<SCubCelSet> subCubCellSetCR(new SCubCelSet(subCubSetCR()));

    // compute the homology model for the bottom level
    CRef<CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> > subHomFiltrCR(new CubCellSetFiltrT<SCubCelSet,FreeChainComplexType>(subCubCellSetCR));
    for(int q=0;q<setEmbDim;++q){
      bettiNumbers[0][q]=subHomFiltrCR().bettiNumber(q);
      fcout << "  Betti[" << q << "] is " << subHomFiltrCR().bettiNumber(q) << std::endl;
      bettiOut << bettiNumbers[0][q] << " ";
    }
    bettiOut << std::endl;
    CRef<BCubSet> supCubSetCR;

    // Now we enter the loop through all starting levels (top level is only target, not a source)
    for(int lev=botLevel;lev<topLevel;++lev){
      Stopwatch sw;
      fcout << " === " << lev << " -> " << lev+1 << " === \n";
      // generate the cubical set for the target level of the current level (i.e. level+1)
      supCubSetCR=makeBCubSet(lev+1);
      if(lev==nLevels-2){
        topCubSetCR=CRef<BCubSet>(new BCubSet(supCubSetCR()));
        fcout << "Registered " << supCubSetCR().cardinality() << " cardinality\n";
      }

      // shaving may speed up computations. However we cannot shave the cubes which were left in the subset.
      if(shave){
        supCubSetCR().shaveWithFixedSubset(subCubSetCR());
        fcout << "Shaving reduced the set to " << supCubSetCR().cardinality() << " cubes" << std::endl;
        //-- if(!( subCubSetCR() <= supCubSetCR() )) throw "Inclusion failed!\n"; // -- MM
      }
      // construct the cellular decomposition of the target
      CRef<SCubCelSet> supCubCellSetCR(new SCubCelSet(supCubSetCR()));
      // and construct the homology model for the target
      Stopwatch swfilt;
      CRef<CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> > supHomFiltrCR(new CubCellSetFiltrT<SCubCelSet,FreeChainComplexType>(supCubCellSetCR));
      fcout << "Construction of the filter took " << swfilt << std::endl;
      if(lev==nLevels-1){
        topHomFiltrCR=subHomFiltrCR;
        topCubCellSetCR=subCubCellSetCR;
//        fcout << "Registered " << subCubCellSetCR().cardinality() << " cardinality\n";
      }

      Stopwatch swincl;

      // Now compute the matrix of the inclusion map in the bases obtained from the homology model
      CRef<std::vector<MatrixType> > subInclMatrixCR=
          InclusionHomology<SCubCelSet,FreeChainComplexType>::CrbIncHom(subHomFiltrCR(),supHomFiltrCR());
      fcout << "Construction of matrices took " << swincl << std::endl;

      // store the computed results, separated by the homology grade dimension,
      // so that after the loop is completed inclusionMatricesCR()[q] contains a vector of matrices for the consecutive
      // filtration levels
      for(int q=0;q<setEmbDim;++q){
        inclusionMatricesCR()[q].push_back(subInclMatrixCR()[q]);
        bettiNumbers[lev+1-botLevel][q]=supHomFiltrCR().bettiNumber(q);
        fcout << "  Betti[" << q << "] is " << supHomFiltrCR().bettiNumber(q) << std::endl;
        if(storeMatrices) imat << subInclMatrixCR()[q] << std::endl;
        bettiOut << bettiNumbers[lev+1-botLevel][q] << " ";

      }
      bettiOut << std::endl;
      fcout << " Computation completed in " << sw << std::endl;
      subHomFiltrCR=supHomFiltrCR;
      subCubSetCR=supCubSetCR;
    }
    fcout << " Total computation time of homology inclusion matrices is " << swtot << std::endl;
  }


  // ******************************************************** //
  int readMatrices(int botLevel,int topLevel){
    inclusionMatricesCR=CRef<GradedFilteredIntMatrix>(new GradedFilteredIntMatrix);
    std::string imatFname=baseName+"imatrices.txt";
    std::ifstream imat(imatFname.c_str());

    fcout << "Reading matrices from " << imatFname.c_str() << std::endl;      // -- MM
    int cnt=0;
    for(int q=0;q<setEmbDim;++q){
      inclusionMatricesCR().push_back(std::vector<MatrixType>());
    }
    for(int lev=botLevel;lev<=topLevel;++lev){
      std::cout << "Reading level " << lev << std::endl;        // -- MM
      for(int q=0;q<setEmbDim;++q){
// -- MM  std::cout << "Reading grade " << q << std::endl;        // -- MM
        if(lev<topLevel){
          try{
            MatrixType Q;
            imat >> Q;
            inclusionMatricesCR()[q].push_back(Q);
// -- MM  std::cout << " Read matrix for level " << lev << " and grade " << q << " with dimensions " << Q.numberOfRows() << "x" << Q.numberOfColumns() << std::endl;            // -- MM
          }catch(std::ios_base::failure){
            return cnt;
          }
        }
      }
      if(lev<topLevel) ++cnt;
      char ch;
      while(' '==(ch=imat.peek()) || ch=='\n') ch=imat.get();
      ch=imat.get();
      if(imat.eof()) return cnt;
      else imat.unget();
    }
    return cnt;
  }

  // ******************************************************** //
  void computePersistenceIntervals(int botLevel,int topLevel,bool simplify){
    // if this is a seperate run, inclusion matrices must be read from disc
    if(inclusionMatricesCR.isNull()){
      std::cout << "Reading" << std::endl;
      if(!topLevel) throw "Use topLevel to provide top level!";
      int nLevels=readMatrices(botLevel,topLevel);
      std::cout << "Read " << nLevels << " matrix levels" << std::endl;
    }
    // Make a shorthand
    GradedFilteredIntMatrix& inclMatrices=inclusionMatricesCR();

    std::string intervalTableFileName=baseName;
    intervalTableFileName+="intervalTable.txt";
    ofstream intervalTableFile(intervalTableFileName.c_str());
    // process every homology grade dimension seperately
    for(int q=0;q<setEmbDim;++q){
      std::cout << " -- Grade " << q << " --- " << std::endl;
      // the whole construction is delegated to the constructor of PersistenceMatrix
      // see the file PersistenceMatrix.hpp for details
      PersistenceMatrix<ScalarType> pm(inclMatrices[q],botLevel);

      if(simplify){
        fcout << " === Simplifying ===\n";
        pm.simplify();
      }else{
        fcout << " === Simplifying skipped ===\n";
      }
fcout << " Finding the remaining persistence intervals\n";
      pm.findRemainingPersistenceIntervals();

      std::string intervalsFileName=baseName;
      intervalsFileName << "intervals.grade" << q << ".txt";
      ofstream intervalsFile(intervalsFileName.c_str());
      intervalsFile << pm.getIntervalList();
      intervalsFile.close();

      std::string intervalPathsFileName=baseName;
      intervalPathsFileName << "intervalPaths.grade" << q << ".txt";
      ofstream intervalPathsFile(intervalPathsFileName.c_str());
      intervalPathsFile << pm.getIntervalPathsList();
      intervalPathsFile.close();

      intervalTableFile << pm.getIntervalTable();
    }
    intervalTableFile.close();

  }

  // ******************************************************** //
  // Used occasionally to understand the structure of matrices
  void checkComplexity(int botLevel,int topLevel){
    std::string complexityFname=baseName+"complexity.txt";
    std::ofstream complexity(complexityFname.c_str());
    Stopwatch swtot;

    if(inclusionMatricesCR.isNull()){
      std::cout << "Reading" << std::endl;
      int nLevels=readMatrices(botLevel,1000);
      std::cout << "Read " << nLevels << " matrix levels" << std::endl;
    }

    for(int lev=botLevel;lev<topLevel;++lev){
      complexity << "    --- Level " << lev << " --- " << std::endl;
      std::cout << "    --- Level " << lev << " --- " << std::endl;
      for(int q=0;q<setEmbDim;++q){
        complexity << "        Grade " << q << ": ";
        MatrixType& A=inclusionMatricesCR()[lev-botLevel][q];
        int m=A.numberOfRows();
        int n=A.numberOfColumns();
        int trivialColCnt=0,simpleColCnt=0;
        for(int j=1;j<=n;++j){
          int nonZeroCnt=0;
          for(int i=1;i<=m;++i) if(A(i,j)!=ScalarType(0)) ++nonZeroCnt;
          if(nonZeroCnt == 0) ++trivialColCnt;
          else if(nonZeroCnt == 1) ++simpleColCnt;
        }
        complexity << trivialColCnt << "|" << simpleColCnt << "|" << n << std::endl;
        int diff=n - trivialColCnt - simpleColCnt;
        if(diff){
          complexity << " Warning: " << diff << " complex generators\n";
          std::cout << " Warning: " << diff << " complex generators\n";
        }
      }
    }
  }


  // ******************************************************** //
  #ifdef _USE_KRAK_
  void drawPersistenceIntervals(int botLevel,int topLevel){
    for(int q=0;q<setEmbDim;++q){
      rootFrame.Clear();
      intervalsFrame.setWorldCoord(-1.,(double)numberOfIntervals[q]*1.05,(double)topLevelBis+1,-(double)numberOfIntervals[q]*0.05);
      intervalsFrame.Bound();
      double y=0;
      double x0=0;
      double x=x0;
      double dx=1;
      for(int blev=botLevel;blev<topLevelBis-1;++blev){
        x=x0+dx;
        for(int elev=blev;elev<topLevelBis;++elev){
          for(int k=0;k<persistenceIntervals;++k){
            ++y;
            intervalsFrame.jump(x0,y);
            intervalsFrame.draw(x,y);
          }
          x+=dx;
        }
        x0+=dx;
      }
      waitBt();
    }
  }
  #endif

  void process(std::string task, int botLevel,int topLevel, bool shave,bool storeMatrices, bool simplify){
    if(task == "all"){
      Stopwatch sw1;
      fcout << "Starting computation of inclusion maps " << sw1  << std::endl;
      findInclusionMaps(botLevel,topLevel,shave,storeMatrices);
      fcout << "Inclusion maps computation time is " << sw1  << std::endl;
      Stopwatch sw2;
      fcout << "Starting computation of persistence intervals " << sw1  << std::endl;
      computePersistenceIntervals(botLevel,topLevel,simplify);
      fcout << "Total persistence intervals computation time is " << sw2  << std::endl;
    }else if(task == "inclusions"){
      findInclusionMaps(botLevel,topLevel,shave,true);
    }else if(task == "intervals"){
      computePersistenceIntervals(botLevel,topLevel,simplify);
    }else if(task == "complexity"){
      checkComplexity(botLevel,topLevel);
    }
    #ifdef _USE_KRAK_
    else if(task == "picture"){
      computePersistentBettiNumbers(botLevel,topLevel);
      computePersistenceIntervals(botLevel,topLevel);
      drawPersistenceIntervals(botLevel,topLevel);
    }
    #endif
  }

  void writeMatchingMatrix(CRef<CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> > homFiltrCR){
    std::string imatFname=baseName+"matchingMatrices.txt";
    std::ofstream imat(imatFname.c_str());
    CRef<SCubCelSet> fullCubCellSetCR(new SCubCelSet(topCubSetCR()));
    CRef<CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> > fullHomFiltrCR(new CubCellSetFiltrT<SCubCelSet,FreeChainComplexType>(fullCubCellSetCR));

    CRef<std::vector<MatrixType> > leftMatchingMatrixCR=
        InclusionHomology<SCubCelSet,FreeChainComplexType>::CrbIncHom(getTopHomFiltr()(),fullHomFiltrCR());
    CRef<std::vector<MatrixType> > rightMatchingMatrixCR=
        InclusionHomology<SCubCelSet,FreeChainComplexType>::CrbIncHom(homFiltrCR(),fullHomFiltrCR());
    for(int q=0;q<setEmbDim;++q){
      imat << "Dimension " << q << " left " << std::endl;
      imat << leftMatchingMatrixCR()[q] << std::endl;
      imat << "Dimension " << q << " right " << std::endl;
      imat << rightMatchingMatrixCR()[q] << std::endl;
    }
  }
}; // class FilteredCubset
#endif


/* ------------------------  ------------------------ */
/// @}

