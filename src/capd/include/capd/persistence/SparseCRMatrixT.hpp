/// @addtogroup persistence
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file SparseCRMatrixT.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (c) Marian  Mrozek, Krakow 2007-2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _SPARSECRMATRIXT_HPP_
#define _SPARSECRMATRIXT_HPP_

#include <vector>


template<typename Chain>
class SparseRowMatrixT;

template<typename Chain>
class SparseColMatrixT;



/* ===================================  =================================== */
template<typename Chain>
class VectorOfChainsT : public std::vector<Chain>{
  protected:
    typedef typename Chain::ScalarType ScalarType;
    typedef typename Chain::iterator iterator;
    typedef typename Chain::const_iterator const_iterator;

  public:
    VectorOfChainsT(int numberOfChains,int maxLengthOfChain):
      std::vector<Chain>(numberOfChains),
      m_numberOfChains(numberOfChains),
      m_maxLengthOfChain(maxLengthOfChain)
    {}

    Chain& entryAt(int i){
      return (*this)[i-1];
    }

    const Chain& entryAt(int i) const{
      return (*this)[i-1];
    }

    void exchange(int i,int j){
      if(i!=j) entryAt(i).swap(entryAt(j));
    }

    void multiply(int i, ScalarType s){
      entryAt(i)*=s;
    }

    void addMultiplicity(int i,int j, ScalarType s){
      entryAt(i).addMultiplicity(entryAt(j),s);
    }

    void setToIdentity(){
      for(int i=1;i<=m_numberOfChains;++i){
        entryAt(i)[i]=ScalarType(1);
      }
    }

    int numberOfNontrivialChains(){
      int cnt=0;
      for(int i=1;i<=m_numberOfChains;++i){
        if( !entryAt(i).isZero() ) ++cnt;
      }
      return cnt;
    }

    bool trivial(){
      return m_numberOfChains==0 || m_maxLengthOfChain == 0;
    }

    void setToTrivial(){
      m_maxLengthOfChain=0;
      for(int i=1;i<=m_numberOfChains;++i){
        entryAt(i)=Chain();
      }
    }

    void swap(VectorOfChainsT& v2){
      this->std::vector<Chain>::swap(*static_cast<std::vector<Chain>*>(&v2));
    }

  protected:
    int m_numberOfChains,m_maxLengthOfChain;
};

/* ===================================  =================================== */
template<typename Chain>
class SparseColMatrixT : public VectorOfChainsT<Chain>{
  protected:
    typedef typename VectorOfChainsT<Chain>::ScalarType ScalarType;
    typedef typename VectorOfChainsT<Chain>::iterator iterator;
    typedef typename VectorOfChainsT<Chain>::const_iterator const_iterator;
  public:

    SparseColMatrixT(int numberOfRows,int numberOfColumns):
      VectorOfChainsT<Chain>(numberOfColumns,numberOfRows)
    {}

    int numberOfRows() const{
      return this->m_maxLengthOfChain;
    }

    int numberOfColumns() const{
      return this->m_numberOfChains;
    }

    void leftMultiply(const SparseRowMatrixT<Chain>& Q){
      int m=Q.numberOfRows();
      int n=this->numberOfColumns();
      SparseColMatrixT<Chain> M(m,n);
      for(int j=1;j<=n;++j){
        Chain& c=this->entryAt(j);
        Chain& d=M.entryAt(j);
        for(int i=1;i<=m;++i){
          ScalarType a=Q.entryAt(i)*c;
          if(a) d.accessAt(i)=a;
        }
      }
      this->swap(M);
    }

    friend std::ostream& operator<<(std::ostream& o, const SparseColMatrixT<Chain>& Q){
      o << "{\n";
      for(int i=1;i<=Q.numberOfRows();++i){
        for(int j=1;j<=Q.numberOfColumns();++j){
          o << Q.entryAt(j).at(i) << " ";
        }
        o << "\n";
      }
      o << "}\n";
      return o;
    }

/*
    int rankOfUpperTriangularMatrix(){
      if(this->trivial()) return 0;
      int m=this->numberOfRows();
      int n=this->numberOfColumns();
      int counter=0;
      for(int i=1;i<=m;++i){
        for(int j=1;j<=n;++j){
          // -- MM  fcout << "i=" << i << " j=" << j << " q=" << Q(i,j) << std::endl;
          if(this->entryAt(j).at(i)){
            ++counter;
            goto nextRow;
          }
        }
        break;
        nextRow:;
      }
      return counter;
    }
*/

    int rankOfUpperTriangularMatrix(){
      if(this->trivial()) return 0;
//      int m=this->numberOfRows();
      int n=this->numberOfColumns();
//      int counter=0;
      int maxIndex=0;
      for(int j=1;j<=n;++j){
        Chain& c=this->entryAt(j);
        const_iterator it=c.begin();
        const_iterator itEnd=c.end();
        for(;it!=itEnd;++it){
          if(it->first > maxIndex) maxIndex=it->first;
        }
      }
      return maxIndex;
    }

    void swap(SparseColMatrixT& v2){
      this->VectorOfChainsT<Chain>::swap(*static_cast<VectorOfChainsT<Chain>*>(&v2));
    }
};

/* ===================================  =================================== */
template<typename Chain>
class SparseRowMatrixT : public VectorOfChainsT<Chain>{
    typedef typename VectorOfChainsT<Chain>::ScalarType ScalarType;
    typedef typename VectorOfChainsT<Chain>::iterator iterator;
    typedef typename VectorOfChainsT<Chain>::const_iterator const_iterator;

  public:

    SparseRowMatrixT(int numberOfRows,int numberOfColumns):
      VectorOfChainsT<Chain>(numberOfRows,numberOfColumns)
    {}

    template<typename MatrixType>
    SparseRowMatrixT(const MatrixType& A_matrix):
      VectorOfChainsT<Chain>(A_matrix.numberOfRows(),A_matrix.numberOfColumns())
    {
      for(int j=1;j<=numberOfColumns();++j){
        for(int i=1;i<=numberOfRows();++i){
          if(A_matrix(i,j)!=0){
            this->entryAt(i)[j]=A_matrix(i,j);
          }
        }
      }
    }

    int numberOfRows() const{
      return this->m_numberOfChains;
    }

    int numberOfColumns() const{
      return this->m_maxLengthOfChain;
    }

    void exchange(VectorOfChainsT<Chain>& Q,int i,int j){
      VectorOfChainsT<Chain>::exchange(i,j);
      Q.exchange(i,j);
    }

    void multiply(VectorOfChainsT<Chain>& Q,int i,ScalarType q){
      this->multiply(i,q);
      Q.multiply(i,q);
    }

    void addMultiplicity(VectorOfChainsT<Chain>& Q,int i,int j,ScalarType q){
      VectorOfChainsT<Chain>::addMultiplicity(i,j,q);
      Q.addMultiplicity(j,i,-q);   // the order of arguments is correct and different from the implementation in intMatrixAlgorithms.cpp
    }

    void rightMultiply(const SparseColMatrixT<Chain>& Q){
      int m=this->numberOfRows();
      int n=Q.numberOfColumns();
      SparseRowMatrixT<Chain> M(m,n);
      for(int i=1;i<=m;++i){
        Chain& c=this->entryAt(i);
        Chain& d=M.entryAt(i);
        for(int j=1;j<=n;++j){
          ScalarType a=c*Q.entryAt(j);
          if(a) d.accessAt(j)=a;
        }
      }
      this->swap(M);
    }

    ScalarType valueAt(int i,int j) const{
      return this->entryAt(i).at(j);
    }

    void partRowReduce(SparseColMatrixT<Chain>& Q,int k,int l){
      int m=this->numberOfRows();
      for(int i=k+1;i<=m;++i){
        ScalarType q=valueAt(i,l)/valueAt(k,l);
        this->addMultiplicity(Q,i,k,-q);
      }
    }

    // find the smallest nonzero entry in the subcolumn [i0:m,j0]
    void smallestNonZero(int i0,int j0,ScalarType& s, int& iOpt){
      s=ScalarType(0);
      for(int i=i0;i<=numberOfRows();++i){
        ScalarType t=valueAt(i,j0);
        if(t<ScalarType(0)) t=-t;
        if( s==ScalarType(0) || (s>t && t>ScalarType(0)) ){
          s=t;iOpt=i;
        }
      }
    }

    // check it the subcolumn [i0:m,j0] is nonzero
    bool nonZero(int i0,int j0){
      for(int i=i0;i<=numberOfRows();++i){
        if(valueAt(i,j0)) return true;
      }
      return false;
    }

    void rowPrepare(SparseColMatrixT<Chain>& Q,int k,int l){
      ScalarType s;
      int i=0;
      this->smallestNonZero(k,l,s,i);
//std::cout << "Exchanging " << k << "," << i << " A is " << *this << std::endl;
      this->exchange(Q,k,i);
//std::cout << "After Exchanging " << k << "," << i << " A is " << *this << std::endl;
    }

    void rowReduce(SparseColMatrixT<Chain>& Q,int k,int l){
      while( nonZero(k+1,l) ){
        this->rowPrepare(Q,k,l);
        this->partRowReduce(Q,k,l);
      }
    }

    void rowEchelon(SparseColMatrixT<Chain>& Q,int &k){
      int m=this->numberOfRows();
      int n=this->numberOfColumns();
      Q.setToIdentity();
      k=0;
      int l=1;
//std::cout << "Before loop start " << k << "," << l << " A is " << *this << std::endl;
      do{
        while(l<=n && !nonZero(k+1,l)) ++l;
        if(l==n+1) break;
        this->rowReduce(Q,++k,l);
//std::cout << "After row reducing at " << k << "," << l << " A is " << *this << std::endl;
      }while(k<m);
    }

    friend std::ostream& operator<<(std::ostream& o, const SparseRowMatrixT<Chain>& Q){
      o << "{\n";
      for(int i=1;i<=Q.numberOfRows();++i){
        for(int j=1;j<=Q.numberOfColumns();++j){
          o << Q.valueAt(i,j) << " ";
        }
        o << "\n";
      }
      o << "}\n";
      return o;
    }

    void swap(SparseRowMatrixT& v2){
      this->VectorOfChainsT<Chain>::swap(*static_cast<VectorOfChainsT<Chain>*>(&v2));
    }
};
#endif
/* ===================================  =================================== */
/// @}

