/// @addtogroup persistence
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file PersistenceMatrix.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (c) Marian  Mrozek, Krakow 2007-2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

/**********************************************************/

#ifndef _PERSISTENCE_MATRIX_HPP_
#define _PERSISTENCE_MATRIX_HPP_

#include "capd/homologicalAlgebra/ChainT.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/auxil/CRef.h"
#include "capd/auxil/stringOstream.h"
#include "capd/persistence/SparseCRMatrixT.hpp"

#include <vector>
#include <iomanip>

/* ------------------------ PersistenceMatrix ------------------------
   PersistenceMatrix is a class which stores the matrices
   of a sequence (filtration) of inclusion homology maps
   and computes and stores the persistence intervals information

   Here:
   "filtered" - vector numbered by the original filtration levels

   SparseIntVector - a sparse vector represented as
   an STL map (index -> coefficient) built for non-zero coefficients only
   and embedded with algebraic vector operations implemented in ChainT template

   SparseIntMatrix - a matrix storage organised as a vector
   of SparseIntVector.


   ------------------------ ----------------- ------------------------ */

template<typename P_Scalar>
class PersistenceMatrix{
  private:
    /* ------------------------ type definitions ------------------------ */

    typedef P_Scalar ScalarType;
    typedef ChainT<std::map<int,ScalarType> > SparseIntVector;
    typedef std::vector<SparseIntVector> SparseIntMatrix;
    typedef std::vector<SparseIntMatrix> FilteredSparseIntMatrix;
    typedef std::vector<CRef<SparseIntMatrix> > FilteredCRefSparseIntMatrix;
    typedef SparseRowMatrixT<SparseIntVector> SparseIntRowMatrix;
    typedef SparseColMatrixT<SparseIntVector> SparseIntColMatrix;

    typedef capd::vectalg::Matrix<ScalarType,0,0> IntMatrix;
    typedef std::vector<IntMatrix> FilteredIntMatrix;
    typedef std::vector<SparseIntRowMatrix> FilteredSparseIntRowMatrix;
    typedef std::vector<int> PersistencePath;
    typedef std::vector<PersistencePath> PersistencePathCollection;
    typedef std::vector<PersistencePathCollection> FilteredPersistencePathCollection;

    /* ------------------------  ------------------------ */
    static inline bool trivial(const IntMatrix& Q){
      return Q.numberOfRows()==0 || Q.numberOfColumns()==0;
    }

    /* ------------------------  ------------------------ */
    static int rankOfUpperTriangularMatrix(const IntMatrix& Q){
      if(trivial(Q)) return 0;
      int m=Q.numberOfRows();
      int counter=0;
      for(int i=1;i<=m;++i){
        const_MatrixIterator<IntMatrix> it=Q.beginOfRow(i);
        const_MatrixIterator<IntMatrix> itEnd=Q.endOfRow(i);
        for(;it<itEnd;it.moveToNextColumn()){
          // -- MM  fcout << "i=" << i << " j=" << j << " q=" << Q(i,j) << std::endl;
          if(*it){
            ++counter;
            goto nextRow;
          }
        }
        break;
        nextRow:;
      }
      return counter;
    }


    /* ------------------------  ------------------------ */
    static int EmbDim(const SparseIntVector& A_v){
      int embDim=0;
      typename SparseIntVector::const_iterator it=A_v.begin();
      typename SparseIntVector::const_iterator itEnd=A_v.end();
      for(;it!=itEnd;++it){
        // WARNING: this assumes that vector coordinates are numbered from zero!
        int coordNumber=it->first+1;
        if(coordNumber > embDim) embDim=coordNumber;
      }
      return embDim;
    }

    /* ------------------------  ------------------------ */
    static int NumberOfRows(const SparseIntMatrix& A_m){
      int rowCount=0;
      typename SparseIntMatrix::const_iterator it=A_m.begin();
      typename SparseIntMatrix::const_iterator itEnd=A_m.end();
      for(;it!=itEnd;++it){
        int embDim=EmbDim(*it);
        if(embDim > rowCount) rowCount=embDim;
      }
      return rowCount;
    }

    /* ------------------------  ------------------------ */
    static std::string toString(const SparseIntMatrix& A_m){
      typename SparseIntMatrix::const_iterator it=A_m.begin();
      typename SparseIntMatrix::const_iterator itEnd=A_m.end();
      std::string s;

      int cnt=0;
      for(;it!=itEnd;++it){
        s << cnt++ << " -> " << *it << "\n";
      }
      return s;
    }

    /* ------------------------  ------------------------ */
    // Used by constructors to initialize the object variables
    void setup(const FilteredSparseIntMatrix& A_sparseMatrixFiltr){
      m_matrixFiltr.reserve(m_numberOfLevels);
      m_validFiltr.reserve(m_numberOfLevels);
      m_inCoimageFiltr.reserve(m_numberOfLevels);
      m_blockedFiltr.reserve(m_numberOfLevels);
      // initialize the space for persistence itervals
      for(int i=0;i<=m_numberOfLevels;++i){
        m_persistenceIntervalCount.push_back(std::vector<int>(m_numberOfLevels+1));
        for(int j=0;j<=m_numberOfLevels;++j) m_persistenceIntervalCount[i].push_back(0);
      }
      // for all persistence levels
      for(int i=0;i<m_numberOfLevels;++i){
        int nGen; // number of generators
        if(i<m_numberOfLevels-1){
          nGen=A_sparseMatrixFiltr[i].size();  // for all except the last level nGen is the number of columns
          m_matrixFiltr.push_back(A_sparseMatrixFiltr[i]); // set the matrix of the map
        }else{
          nGen=(
            m_numberOfGeneratorsForTheLastLevel ?
            m_numberOfGeneratorsForTheLastLevel :
            NumberOfRows(A_sparseMatrixFiltr[m_numberOfLevels-2])
          ); // for the last level nGen is the number of rows of the last matrix
          m_matrixFiltr.push_back(SparseIntMatrix(nGen));  // closing with a zero map from the last level
        }
        std::vector<bool> bTrue(nGen),bFalse(nGen);
        for(int i=0;i<nGen;++i){
          bTrue[i]=true;
          bFalse[i]=false;
        }
        m_validFiltr.push_back(bTrue);
        m_inCoimageFiltr.push_back(bTrue);
        m_blockedFiltr.push_back(bFalse);

        PersistencePathCollection emptyCollection;
        m_filteredPersistencePathCollection.push_back(emptyCollection);
      }
    }



  public:
    /* ------------------------ constructor ------------------------ */
    // It seems that currently this constructor is not needed
    PersistenceMatrix(
      const FilteredSparseIntMatrix& A_sparseMatrixFiltr,
      int A_bottomLevelIndex=0
    ):
      m_numberOfLevels(A_sparseMatrixFiltr.size()+1),
      m_numberOfGeneratorsForTheLastLevel(0),
      m_bottomLevelIndex(A_bottomLevelIndex),
      m_persistenceIntervalCount(m_numberOfLevels+1)
    {
      setup(A_sparseMatrixFiltr);
    }

    /* ------------------------ constructor ------------------------ */
    // This constructor is used in cubPersistenceMD.cpp
    PersistenceMatrix(
      const FilteredIntMatrix& A_matrixFiltr,
      int A_bottomLevelIndex=0
    ):
      m_numberOfLevels(A_matrixFiltr.size()+1),
      m_bottomLevelIndex(A_bottomLevelIndex),
      m_persistenceIntervalCount(m_numberOfLevels+1)
    {
      fcout << "Number of levels is " << m_numberOfLevels << std::endl;        // -- MM

      int numberOfSourceLevels=m_numberOfLevels-1;

      // prepare an empty sparseMatrixFiltr
      // note that this is an auxiliary variable
      // its contents will be transfered to the object variable
      // via the setup method at the end
      FilteredSparseIntMatrix sparseMatrixFiltr(numberOfSourceLevels);
      // and fill it with contents from A_matrixFiltr

      // go through all source levels
      for(int lev=0;lev<numberOfSourceLevels;++lev){
// -- MM  std::cout << " level " << lev << ":" << A_matrixFiltr[lev].numberOfRows() << "x" << A_matrixFiltr[lev].numberOfColumns() << std::endl;        // -- MM
        // check the consistency of dimensions
        if(
          lev>0 &&
          A_matrixFiltr[lev-1].numberOfRows() != 0 &&
          A_matrixFiltr[lev].numberOfColumns() != 0 &&
          A_matrixFiltr[lev-1].numberOfRows() != A_matrixFiltr[lev].numberOfColumns()
        ){
          std::string s;
          s << "Inconsistent matrix dimensions for level " << lev << "\n";
          throw s;
        }
        // get the dimensions for the matrix at level lev
        // in particualr n is also the number of generators for level lev
        int n=A_matrixFiltr[lev].numberOfColumns();
        int m=A_matrixFiltr[lev].numberOfRows();
        // when the matrix has no rows or columns (empty matrix),
        // it is always stored as the zero matrix
        // if this is the case, then n as the number of generators may be reconstructed
        // from the number of rows of the previous matrix
        if(n==0 && lev>0) n=A_matrixFiltr[lev-1].numberOfRows();
        // Now go through all generators for the current level
        for(int j=1;j<=n;++j){
          // start with storing an empty sparse vector
          sparseMatrixFiltr[lev].push_back(SparseIntVector());
          // go through all the generators on the respective target level
          for(int i=1;i<=m;++i){
            // and store nonzero entries
            if(A_matrixFiltr[lev](i,j)!=0){
              sparseMatrixFiltr[lev][j-1].accessAt(i-1)=A_matrixFiltr[lev](i,j);
            }
          }
        }
      }
      // the number of generators of the last level must be restored from the number
      // of rows of the last matrix
      m_numberOfGeneratorsForTheLastLevel=A_matrixFiltr[numberOfSourceLevels-1].numberOfRows();
      // finally transfer the sparse matrix to the object variable
      // and initialize the other object variables
      setup(sparseMatrixFiltr);
    }

    /* ------------------------  ------------------------ */
    // Export the filtr of the remaining matrices
    // Do it for all original source levels, but without the added
    // source level whose matrix is zero anyway
    // Needed in the old version of findRemainingPersistenceIntervals
    //  ========= It seems to be not needed anymore! ===========
    CRef<FilteredIntMatrix> exportMatrixFiltr(){
      CRef<FilteredIntMatrix> matrixFiltrCR(new FilteredIntMatrix());
      std::vector<int> dimensions(m_numberOfLevels);
      for(int lev=0;lev<m_numberOfLevels;++lev){
        int count=0;
        for(unsigned int i=0;i<m_matrixFiltr[lev].size();++i){
          if(m_validFiltr[lev][i]) ++count;
        }
        dimensions[lev]=count;
//std::cout << "m_matrixFiltr[lev].size()=" << m_matrixFiltr[lev].size() << std::endl;// *DBG*
      }
      for(int lev=0;lev<m_numberOfLevels-1;++lev){
        matrixFiltrCR().push_back(IntMatrix(dimensions[lev+1],dimensions[lev]));
        int cj=0;
        for(unsigned int j=0;j<m_matrixFiltr[lev].size();++j){
          if(m_validFiltr[lev][j]){
            int ci=0;
            for(unsigned int i=0;i<m_matrixFiltr[lev+1].size();++i){
              if(m_validFiltr[lev+1][i]){
                int coef=0;
                typename SparseIntVector::const_iterator it=m_matrixFiltr[lev][j].find(i);
                if(it!=m_matrixFiltr[lev][j].end()) coef=it->second;
                matrixFiltrCR()[lev][ci++][cj]=coef;
              }
            }
            ++cj;
          }
        }
// -- MM  std::cout << " level " << lev << " Extracted matrix: " << matrixFiltrCR()[lev].numberOfRows() << "x" << matrixFiltrCR()[lev].numberOfColumns() << std::endl;        // -- MM
      }
      return matrixFiltrCR;
    }



    /* ------------------------  ------------------------ */
    // Export the filtr of the remaining matrices
    // Do it for all original source levels, but without the added
    // source level whose matrix is zero anyway
    // used in the method findRemainingPersistenceIntervals
    CRef<FilteredSparseIntRowMatrix> exportSparseIntRowMatrixFiltr(){
      CRef<FilteredSparseIntRowMatrix> matrixFiltrCR(new FilteredSparseIntRowMatrix());
      std::vector<int> dimensions(m_numberOfLevels);
      for(int lev=0;lev<m_numberOfLevels;++lev){
        int count=0;
        for(unsigned int i=0;i<m_matrixFiltr[lev].size();++i){
          if(m_validFiltr[lev][i]) ++count;
        }
        dimensions[lev]=count;
        if(count) fcout << "On level " << lev << " there are " << count << " generators left after simplification\n";
        else fcout << "!!! On level " << lev << " there are no generators left after simplification\n";
//std::cout << "m_matrixFiltr[lev].size()=" << m_matrixFiltr[lev].size() << std::endl;// *DBG*
      }
      for(int lev=0;lev<m_numberOfLevels-1;++lev){
        matrixFiltrCR().push_back(SparseIntRowMatrix(dimensions[lev+1],dimensions[lev]));
        int cj=0;
        for(unsigned int j=0;j<m_matrixFiltr[lev].size();++j){
          if(m_validFiltr[lev][j]){
            int ci=0;
            ++cj;
            for(unsigned int i=0;i<m_matrixFiltr[lev+1].size();++i){
              if(m_validFiltr[lev+1][i]){
                ++ci;
                typename SparseIntVector::const_iterator it=m_matrixFiltr[lev][j].find(i);
                if(it!=m_matrixFiltr[lev][j].end()){
                  matrixFiltrCR()[lev].entryAt(ci)[cj]=it->second;
                }
              }
            }
          }
        }
// -- MM  std::cout << " level " << lev << " Extracted matrix: " << matrixFiltrCR()[lev].numberOfRows() << "x" << matrixFiltrCR()[lev].numberOfColumns() << std::endl;        // -- MM
      }
      return matrixFiltrCR;
    }

    /* ------------------------  ------------------------ */
    // used in simplify()
    void updateInCoimage(int level){
      if(level<=0) return;
      // We will pick up elements which are not in the coimage,
      // so originally mark every generator as contained in the coimage
      for(unsigned int i=0;i<m_matrixFiltr[level].size();++i){
        m_inCoimageFiltr[level][i]=true;
      }

      for( // every (i-th) generator on level-1
        unsigned int i=0;
        i<m_matrixFiltr[level-1].size();
        ++i
      ){
        for( // every non-zero element in the i-th column of the inclusion matrix
          typename SparseIntVector::const_iterator it=m_matrixFiltr[level-1][i].begin();
          it!=m_matrixFiltr[level-1][i].end();
          ++it
        ){
          if(it->second!=0){ // if the element is indeed non-zero
            // mark the respective generator as not contained in the coimage
            m_inCoimageFiltr[level][it->first]=false;
          }
          if(m_blockedFiltr[level-1][i]){ // if i-th generator on level-1 is blocked
            // also mark the "follower" as blocked
            m_blockedFiltr[level][it->first]=true;
          }
        }
      }
    }

    /* ------------------------  ------------------------ */
    static const int S_trivialImg=-1;   // trivial image
    static const int S_complexImg=-2;   // complex image

    /* ------------------------  ------------------------ */
    // The purpose of this method, used in simplify(int level) is to determine
    // the type of image of the generator
    // If there is exactly one non-zero element in this column
    // then the generator is mapped to a generator
    // and then we return just the number of the generator in the image
    // Otherwise either the whole column is zero and we return  S_trivialImg
    // or the coulmn contains more than one non-zero element and we return S_complexImg

    int getImageType(int level,int gen){
      SparseIntVector& v=m_matrixFiltr[level][gen];
      typename SparseIntVector::const_iterator it=v.begin();
      typename SparseIntVector::const_iterator itEnd=v.end();
      int result=S_trivialImg;
      // for every element in the column of generator gen
      for(;it!=itEnd;++it){
// -- MM  std::cout << "        Trying (" << it->first << "," << it->second  << ")" << std::endl;
        if(
          m_validFiltr[level+1][it->first] &&
          it->second != 0
        ){
// -- MM  std::cout << "        Result is  " << result << std::endl;
          if(result>=0) return S_complexImg;
          else result=it->first;
// -- MM  std::cout << "        Continuing with result " << result << std::endl;
        }
      }
      return result;  // anything greater or equal to zero means simple type
    }

    /* ------------------------  ------------------------ */
    // Some generators of persistence homology may be found by tracing
    // the generator from the bottom level under the assumption that
    // in the matrix the respective column contains exactly one non-zero entry
    // which is a unit. This is much faster then crunching zeros.
    bool simplify(int level){
      bool success=false;
// -- MM  std::cout << "    Size is " << m_matrixFiltr[level].size() << std::endl;
      for( // every (i-th) generator on the level level
        unsigned int i=0;
        i<m_matrixFiltr[level].size();
        ++i
      ){
// -- MM  std::cout << "    Trying generator " << i << " on level " << level << std::endl;
        // if the generator is not in the the image and valid,
        // it is a starting point for a persistence interval
        // we need to go ahead and find the whole interval
        if(m_inCoimageFiltr[level][i] && m_validFiltr[level][i]){
// -- MM  std::cout << "    accepted " << i << std::endl;
          // Prepare for forward search
          // std::vector<int> visited; // stack for generators contained in the interval
          PersistencePath visited; // stack for generators contained in the interval
          int cLevel=level;         // current visited level
          int cGen=i;               // current generator (on the current level)
          bool found=false;         // indicator if search succeeded (it may fail)
          while(true){
// -- MM  std::cout << "Passing gen " << cGen << " on lev " << cLevel << std::endl;
            // blocked generators are disregarded and the search fails
            if(m_blockedFiltr[cLevel][cGen]) break;
            // number of generators
            int nGen=m_matrixFiltr[cLevel].size();

            // Situation when cGen>=nGen may happen when the next matrix is trivial and stored as empty matrix
            // It means that the generator is mapped to zero
            if(cGen>=nGen){
// -- MM  std::cout << "cGen= " << cGen << " >= nGen=" << nGen << " on lev " << cLevel << std::endl;
              visited.push_back(cGen);
              found=true;
              break;
            }

            // When an invalid generator is encountered,
            // we treat it as zero detected late
            if(!m_validFiltr[cLevel][cGen]){
// -- MM  std::cout << "cGen not valid" << std::endl;
              --cLevel; // invalid generator is treated as zero but detected one level later than the normal zero
              found=true;
              break;
            }

            // Now we can look ahead for the value
            // At this stage we know that the generator must be invalidated
            // when leaving the loop with found = true, so push it on the stack
            visited.push_back(cGen);
            // nextGen contains the number of the generator in the image
            // if there is exactly one element in the image
            // or S_trivialImg if there is nothing in the image
            // or S_complexImg otherwise
            int nextGen=getImageType(cLevel,cGen);
// -- MM  std::cout << "Next gen, if accepted, will be " << cGen << std::endl;
            // trivial image: the interval was found
            if(nextGen==S_trivialImg){
// -- MM  std::cout << "v.isZero()" << std::endl;
              found=true;
              break;
            // complex image: the interval not found
            // the current generator must be blocked
            }else if(nextGen==S_complexImg){
              m_blockedFiltr[cLevel][cGen]=true;
// -- MM  std::cout << "v is complex" << std::endl;
              break;
            // otherwise we can continue the search of the interval
            }else{
              // next generator becomes the current generator
              cGen=nextGen;
              // we increase the current level
              ++cLevel;
              // this should actually never happen
              if(cLevel==m_numberOfLevels) throw "cLevel reached m_numberOfLevels";
            }
          }
          // If an interval was found we
          // mark all generators on the interval path as not valid
          // (meaning already used) and update the counter of intervals found
          if(found){
// -- MM  std::cout << "Adding interval " << level << "," << cLevel << std::endl;
            for(unsigned int i=0;i<visited.size();++i){
// -- MM  std::cout << "  invalidating " << visited[i] << " on level " << level+i << std::endl;
              m_validFiltr[level+i][visited[i]]=false;
            }
            ++m_persistenceIntervalCount[level][cLevel];
            success=true;
            // store the path
            m_filteredPersistencePathCollection[level].push_back(visited);
          }
        }
      }
      return success;
    }

    /* ------------------------  ------------------------ */
    // Go through all filtration levels
    //
    void simplify(){
//std::cout << "Number of levels is " << m_numberOfLevels << std::endl;
      for( // every level
        int level=0;
        level<m_numberOfLevels;
        ++level
      ){
//        fcout << "Simplifying level " << level+m_bottomLevelIndex << std::endl;

//int cnt=0;
        // perform the simplification preceded by the update in coimage as long
        // as possible
        while(true){
          for(int lev=level;lev<m_numberOfLevels;++lev) updateInCoimage(lev);
//std::cout << "  Starting pass no " << ++cnt << std::endl;
          if(!simplify(level)) break;
        }
//std::cout << "Closing level " << level << std::endl;
      }
    }


    /* ------------------------  ------------------------ */
    // The main method for finding persistence intervals
    // It may be used immediately after the construcion of PersistenceMatrix
    // or just after the simplify method which extracts persistence intervals
    // Used in computePersistenceIntervals in cubPersistenceMD
    void findRemainingPersistenceIntervals(){
      Stopwatch swtot;
      // We use the standard linear algebra approach to find the remaining persistence intervals
      // For this we need the remaining maps in the matrix form
      CRef<FilteredSparseIntRowMatrix> matrixFiltrCR=exportSparseIntRowMatrixFiltr();

      //assert(matrixFiltrCR().size() == (unsigned int)m_numberOfLevels-1);

      /****
        First we bring the matrices to triangular form in the following way
        Let A_k denote the inclusion matrix from level k to level k+1 and let Q_0 be the identity matrix
        We construct B_k and Q_{k+1} such that B_k is in row-echelon form
        and
            B_k=Q_{k+1}^{-1} A_k Q_k
        Then the composition of consecutive B_k is also in row echelon form.
        Moreover, it is conjugate to the respective composition of A_k, so these
        compositions have the same rank but in case of B_k finding the rank is
        straightforward
       ****/

      CRef<SparseIntColMatrix> Q; // to store the Q_k matrices
      for(int lev=0;lev<m_numberOfLevels-1;++lev){ // We have m_numberOfLevels-1 matrices
        SparseIntRowMatrix& A=matrixFiltrCR()[lev];
        if(lev==0 && !A.trivial()){
          int n=A.numberOfColumns();
          Q=CRef<SparseIntColMatrix>(new SparseIntColMatrix(n,n) );
          Q().setToIdentity(); // Q_0 is identity
        }
fcout << "  Triangularization for level=" << lev << " with " << A.numberOfRows() << " rows and " << A.numberOfColumns() << " columns\n";        // -- MM
        int k;
        if(!A.trivial()){ // for a non-empty matrix
          A.rightMultiply(*Q);  // A stores A_k Q_k
          int m=A.numberOfRows();
          Q=CRef<SparseIntColMatrix>(new SparseIntColMatrix(m,m));
          Q().setToIdentity();  // this is done inside rowEchelon, so should be removed from here
          A.rowEchelon(*Q,k);   // A stores B_k and is in row echelon form, Q stores Q_{k+1}
        }else{
          if(lev<m_numberOfLevels-2){
            int n=matrixFiltrCR()[lev+1].numberOfColumns();
            Q=CRef<SparseIntColMatrix>(new SparseIntColMatrix(n,n) );
            Q().setToIdentity();
          }
        }
      }
      /****

        Triangularization is now completed, i.e.
        matrixFiltrCR() stores the matrices B_k in row echelon form

        Now we are ready to compute the persistent Betti numbers.
        For this we need to compute the compositions of the matrices A_i over every interval [I,J],i.e.
        A_J A_{J-1} ... A_I

      ****/
      std::vector<std::vector<int> > persistentBettiNumbers(m_numberOfLevels+1);
      SparseIntRowMatrix TrivialMatrix(0,0);
      for(int bLev=0;bLev<=m_numberOfLevels;++bLev){
std::cout << "  Computing persistent Betti numbers from level=" << bLev << std::endl;   // -- MM
        persistentBettiNumbers[bLev].reserve(m_numberOfLevels+1);
        // We start with the identity matrix for level bLev of size n with n defined as
        int n=(
          bLev<m_numberOfLevels-1 ?
          matrixFiltrCR()[bLev].numberOfColumns() :
          (bLev>m_numberOfLevels-1 ? 0 : matrixFiltrCR()[bLev-1].numberOfRows() )
        );
//std::cout << "n is " << n << std::endl;

        SparseIntColMatrix AIJ(n,n); // Here we will compute the composition of the matrices A_i
        AIJ.setToIdentity();         // We start with the identity matrix, no composition computed yet
        for(int eLev=bLev;eLev<=m_numberOfLevels;++eLev){
//fcout << "  Computing persisten Betti numbers from level=" << bLev << " to level " << eLev << std::endl;   // -- MM
          if(eLev<m_numberOfLevels){
            // AIJ is triangular, so its rank is equal to its number of nontrivial rows or columns
            persistentBettiNumbers[bLev][eLev]=AIJ.rankOfUpperTriangularMatrix();
            if(!AIJ.trivial()){
              SparseIntRowMatrix& A=(eLev<m_numberOfLevels-1 ? matrixFiltrCR()[eLev] : TrivialMatrix );
              if(A.trivial()){
                AIJ.setToTrivial(); // the product by a trivial matrix is a trivial matrix
              }else{
                AIJ.leftMultiply(A); // otherwise we left multiply by A
              }
              //std::cout << "AIJ has " << AIJ.numberOfRows() << " rows\n";// *DBG*
            }
          }else{
            persistentBettiNumbers[bLev][eLev]=0;
          }
//std::cout << "persistentBettiNumbers " << bLev  << "  " << eLev  << "  "  << persistentBettiNumbers[bLev][eLev]  << "  "  << std::endl;
        }
      }

      /****

           Finally we are ready to compute the number of persistence intervals

           The cardinality of (k,l) persistence interval is given by
              pb(k,l) - pb(k-1,l) - ( pb(k,l+1) - pb(k-1,l+1) )
           where pb(k,l) is the (k,l) persistent Betti number.
           Since the boundary cases of the persistent Betti numbers (which are to be treated
           as zero) are not included in the persistentBettiNumbers,
           we first define the following macro

      ****/

      #define getPB(blev,elev) \
      ( blev>=0 && blev<=m_numberOfLevels && elev>=0 && elev<=m_numberOfLevels ?  \
          persistentBettiNumbers[blev][elev] : 0)

      bool updateNeeded=false;
      for(int bLev=0;bLev<=m_numberOfLevels;++bLev)
      for(int eLev=bLev;eLev<=m_numberOfLevels;++eLev){
        int k=
          +getPB(bLev  ,eLev  )
          -getPB(bLev-1,eLev  )
          -getPB(bLev  ,eLev+1)
          +getPB(bLev-1,eLev+1)
        ;
        m_persistenceIntervalCount[bLev][eLev]+=k;
//std::cout << "Updated " << bLev  << "  " << eLev  << "  "  << k  << "  "  << std::endl;

        if(k) updateNeeded=true;
      }
      if(updateNeeded){
        std::cout << "Persistence intervals of the remaining filter computed in " << swtot << "\n\n";
      }
    }

    /* ------------------------  ------------------------ */
    // produce printable (in string form) output of persistence intervals
    std::string getIntervalTable(){
      std::ostringstream s;
      for(int i=0;i<m_numberOfLevels;++i){
        for(int j=0;j<m_numberOfLevels;++j){
          if(j>=i){
            s << setw(4)  <<  m_persistenceIntervalCount[i][j];
          }else{
            s << setw(4) << " -";
          }
        }
        s  << "\n";
      }
      return s.str();
    }

    /* ------------------------  ------------------------ */
    std::string getIntervalList(){
      std::string s;
      for(int i=0;i<=m_numberOfLevels-1;++i){
        for(int j=0;j<=m_numberOfLevels;++j){
          if(j>=i){
            for(int k=0;k<m_persistenceIntervalCount[i][j];++k){
              s << i+m_bottomLevelIndex << " " << j+m_bottomLevelIndex << "\n";
            }
          }
        }
      }
      return s;
    }

    /* ------------------------  ------------------------ */
    std::string getIntervalPathsList(){
      std::string s;
      for(unsigned int lev=0;lev<m_filteredPersistencePathCollection.size();++lev){
        s << "Paths starting from level " <<  m_bottomLevelIndex+lev << "\n";
        for(unsigned int i=0;i<m_filteredPersistencePathCollection[lev].size();++i){
          for(unsigned int j=0;j<m_filteredPersistencePathCollection[lev][i].size();++j){
            s << m_filteredPersistencePathCollection[lev][i][j] << " ";
          }
          s << "\n";
        }
      }
      return s;
    }

    /* ------------------------  ------------------------ */

  private:
    // the original number of levels,
    // without the extra level added as the target for the final zero map
    // NOTE:
    // the original number of source levels, i.e levels where the inclusion maps originate, is one less
    // and the total number of levels, i.e. including the extra target level for the final zero map is one more
    int m_numberOfLevels;

    // the number of generators for the last (target) level cannot be deduced
    // from the matrix filter, so it must be stored separately
    int m_numberOfGeneratorsForTheLastLevel;
    // Internally all levels are numbered from zero
    // the bottom level index is added for external presentation
    int m_bottomLevelIndex;

    // the sequence of matrices of homology inclusion maps
    FilteredSparseIntMatrix m_matrixFiltr;

    // markers of generators which are in coimage (natural candidates for the starting points of interval paths)
    std::vector<std::vector<bool> > m_inCoimageFiltr;
    // generators on detected interval paths are marked as not valid (should not be considered anymore)
    std::vector<std::vector<bool> > m_validFiltr;
    // generators whose image contains more than one generator
    // do not lead to interval paths and are marked as blocks
    std::vector<std::vector<bool> > m_blockedFiltr;

    // storage for the computed number of persistence intervals
    std::vector<std::vector<int> >  m_persistenceIntervalCount;

    // storage for the computed persistence paths
    FilteredPersistencePathCollection m_filteredPersistencePathCollection;
};
#endif
/// @}

