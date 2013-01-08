/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file MatrixIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_VECTALG_MATRIXITERATOR_H_ 
#define _CAPD_VECTALG_MATRIXITERATOR_H_ 

#include <utility>
#include <iostream>

template<typename Matrix>
class MatrixIterator{
public:
  typedef typename Matrix::ScalarType ScalarType;
  MatrixIterator(const Matrix& A_matrix):
     m_Matrix(A_matrix),
     m_pStart(const_cast<ScalarType*>(A_matrix.at(1,1))),
     m_pEntry(const_cast<ScalarType*>(A_matrix.at(1,1))),
     m_nNextRowJump(A_matrix.rowStride()),
     m_nNextColumnJump(A_matrix.columnStride()){
  }
  MatrixIterator(const Matrix& A_matrix,ScalarType* A_pEntry):
     m_Matrix(A_matrix),
     m_pStart(const_cast<ScalarType*>(A_matrix.at(1,1))),
     m_pEntry(const_cast<ScalarType*>(A_pEntry)),
     m_nNextRowJump(A_matrix.rowStride()),
     m_nNextColumnJump(A_matrix.columnStride()){
  }
  MatrixIterator& moveToNextColumn(){
    m_pEntry+=m_nNextColumnJump;
    return *this;
  }
  MatrixIterator& moveToPrevColumn(){
    m_pEntry-=m_nNextColumnJump;
    return *this;
  }
  MatrixIterator& moveToNextRow(){
    m_pEntry+=m_nNextRowJump;
    return *this;
  }
  MatrixIterator& moveToPrevRow(){
    m_pEntry-=m_nNextRowJump;
    return *this;
  }
  ScalarType& operator*() const{
    return *m_pEntry;
  }
  bool operator<(const MatrixIterator A_it2) const{
    return this->m_pEntry < A_it2.m_pEntry;
  }
  MatrixIterator& operator=(const MatrixIterator A_it2){
    this->m_pStart = A_it2.m_pStart;
    this->m_pEntry = A_it2.m_pEntry;
    this->m_nNextRowJump = A_it2.m_nNextRowJump;
    this->m_nNextColumnJump = A_it2.m_nNextColumnJump;
    return *this;
  }
  std::pair<int,int> rowAndColumn() const{
    int dist=m_pEntry-m_pStart;
    return ( m_nNextColumnJump == 1 ?
      std::pair<int,int>(1+dist/this->m_nNextRowJump,1+dist%this->m_nNextRowJump) :
      std::pair<int,int>(1+dist%this->m_nNextColumnJump,1+dist/this->m_nNextColumnJump)
    );
  }
  int row() const{
    int dist=m_pEntry-m_pStart;
    return ( m_nNextColumnJump == 1 ?
      1+dist/this->m_nNextRowJump :
      1+dist%this->m_nNextColumnJump
    );
  }
  int column() const{
    int dist=m_pEntry-m_pStart;
    return ( m_nNextColumnJump == 1 ?
      1+dist%this->m_nNextRowJump :
      1+dist/this->m_nNextColumnJump
    );
  }

protected:
  const Matrix& m_Matrix;
  ScalarType* m_pStart;
  ScalarType* m_pEntry;
  int m_nNextRowJump,m_nNextColumnJump;
public:
  friend std::ostream& operator<<(std::ostream& o,const MatrixIterator& it){
    std::pair<int,int> p=it.rowAndColumn();
    o << " m_pStart= " << (int)it.m_pStart << " m_pEntry= " << (int)it.m_pEntry << " at " << p.first << "," << p.second << ":" << *it;
    return o;
  }
};

template<typename Matrix>
class const_MatrixIterator : public MatrixIterator<Matrix>{
public:
  typedef typename Matrix::ScalarType ScalarType;
  const_MatrixIterator(const Matrix& A_matrix) : MatrixIterator<Matrix>(A_matrix){}
  const_MatrixIterator(const Matrix& A_matrix,ScalarType* A_pEntry):MatrixIterator<Matrix>(A_matrix,A_pEntry){}
  const_MatrixIterator(const Matrix& A_matrix,const ScalarType* A_pEntry):MatrixIterator<Matrix>(A_matrix,const_cast<ScalarType*>(A_pEntry)){}
  const_MatrixIterator(const MatrixIterator<Matrix>& A_it) : MatrixIterator<Matrix>(A_it){}
  const_MatrixIterator& operator=(const const_MatrixIterator A_it2){
    this->m_pStart = A_it2.m_pStart;
    this->m_pEntry = A_it2.m_pEntry;
    this->m_nNextRowJump = A_it2.m_nNextRowJump;
    this->m_nNextColumnJump = A_it2.m_nNextColumnJump;
    return *this;
  }
  const ScalarType& operator*() const{
    return *this->m_pEntry;
  }
};

#endif // _CAPD_VECTALG_MATRIXITERATOR_H_ 

/// @}
