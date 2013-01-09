/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ECellMDCodeT.h
///
/// @author Marian Mrozek
/// UNDER CONSTRUCTION !!!!!!
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_ECELLMDCODE_H_)
#define _ECELLMDCODE_H_

#include <iostream>
#include <sstream>
#include <vector>
#include <map>



//template<typename cluster,int dim, typename P_Scalar=int>
template<typename cluster,int dim>
class ECellMDCodeT;


//template<typename cluster,int dim, typename P_Scalar>
template<typename cluster,int dim>
std::ostream& operator<<(std::ostream& out,const ECellMDCodeT<cluster,dim>& A_cu);
template<typename cluster,int dim>
std::istream& operator>>(std::istream& inp,ECellMDCodeT<cluster,dim>& A_cu);

// ********** class ECellMDCodeT ********** //
/*
    This class is used to code elementary cells as described in
    M. Mrozek, K. Mischaikow and T. Kaczynski,
    Computational Homology,
    Applied Mathematical Sciences 157, Springer-Verlag, New York, 2004

    The coding consist in packing the coordinates of the intervals of the cell in one word,
    with the coordinate of the lowest dimension in the lowest bits of the word

    The coordinate of the interval of the cell is the sum of its endpoints, i.e.
    the coordinate of the degenerate interval [k,k] is 2k  and
    the coordinate of the nondegenerate interval (k,k+1) is 2k+1

    The capacity of this coding depends on dimension and the cluster used as word.
    For instance a 32 bit word in dimesion 3 can accommodate coordinates from 0 up to 2^10-1=1023, i.e.
    intervals [0,0], (0,1), [1,1], ... (510,511), [511,511], (511,512)
*/
template<typename cluster,int dim>
class ECellMDCodeT{
private:
  static const unsigned int bitsPerDimension=8*sizeof(cluster)/dim;
  static const cluster unit=1;
  static const cluster mask=( dim ==1 ? ~((cluster)0) : (unit << bitsPerDimension)-1);
public:
  typedef cluster ClusterType;
//  typedef P_Scalar ScalarType;  // Note: ScalarType needed only when exporting boundary and coboundary for coefficients!!!
  const static int setEmbDim=dim;
  ECellMDCodeT():m_code(0){}
  // Warning, this constructor is a temporary, unsafe shortcut
  // It shoud be replaced by a constructor which takes as argument a vector
  // of elements of class CellCoordCode(to be written)
  ECellMDCodeT(const int A_c[],int):m_code(A_c[dim-1]){
    for(int i=dim-2;i>=0;--i){
      (m_code <<= bitsPerDimension) |= A_c[i];
    }
  }
  ECellMDCodeT(const ElementaryCell& A_c):m_code(A_c.coords()[dim-1]){
    for(int i=dim-2;i>=0;--i){
      (m_code <<= bitsPerDimension) |= A_c.coords()[i];
    }
  }

  // construct the j-th left or right face
  ECellMDCodeT(const ECellMDCodeT& A_ec,int j,bool right):m_code(A_ec.m_code){
      if(right){
        m_code+=(unit << j*bitsPerDimension);
      }else{
        m_code-=(unit << j*bitsPerDimension);
      }
  }
  // construct the j-th left or right coface
  //(Note: it differs from the above constructor only by the order of arguments
  // and in this coding the body is the same as above
  ECellMDCodeT(const ECellMDCodeT& A_ec,bool right,int j):m_code(A_ec.m_code){
    if(right){
      m_code+=(unit << j*bitsPerDimension);
    }else{
      m_code-=(unit << j*bitsPerDimension);
    }
  }
  ECellMDCodeT(const char* c):m_code(0){
    std::istringstream s(c);
    s >> *this;
  }

  // Needed for compability with other codes, the set not needed
  template<typename P_Set>
  ECellMDCodeT(const P_Set&,const ECellMDCodeT& A_ec):m_code(A_ec.m_code){}

  // Needed for projection maps
//  template<int altDim>
//  explicit ECellMDCodeT(ECellMDCodeT<cluster,altDim,P_Scalar> A_code, bool A_left=false):m_code(0){
  template<typename P_altCluster,int altDim>
  explicit ECellMDCodeT(ECellMDCodeT<P_altCluster,altDim> A_code, bool A_left=false):m_code(0){
    int shift=(A_left ? altDim-dim : 0);
    for(int i=dim-1;i>=0;--i){
      (m_code <<= bitsPerDimension) |= A_code.getValAtCoord(i+shift);
    }
  }


  template<typename P_iterator>
  explicit ECellMDCodeT(const P_iterator& A_iterator):m_code(A_iterator[dim-1]){
    for(int i=dim-2;i>=0;--i){
      (m_code <<= bitsPerDimension) |= A_iterator[i];
    }
  }

  static unsigned int maxValAtCoord(int i){
    return ( (~(cluster)0) >> bitsPerDimension*i) & mask;
  }

  void getVals(unsigned int vals[]) const{
    cluster code=m_code;
    for(int i=0;i<dim;++i){
      vals[i]=code & mask;
      code >>= bitsPerDimension;
    }
  }

  unsigned int getValAtCoord(int i) const{
    return (m_code >> bitsPerDimension*i) & mask;
  }

  void setValAtCoord(int i,unsigned int val){
    (m_code &= ~(mask << bitsPerDimension*i)) |= (val << bitsPerDimension*i);
  }

  bool nonDegenerateAtCoord(int i) const{
    return (m_code >> bitsPerDimension*i) & unit;
  }

  int embDim() const{return dim;}
  int ownDim() const{
    int d=0;
    for(unsigned int i=0;i<dim;++i){
      if(nonDegenerateAtCoord(i)) ++d;
    }
    return d;
  }
  bool operator<(const ECellMDCodeT A_ec2) const{
    return m_code < A_ec2.m_code;
  }

  void primaryFaces(std::vector<ECellMDCodeT>& A_primaryFaces) const{
    for(unsigned int i=0;i<dim;++i){
      if(nonDegenerateAtCoord(i)){
        A_primaryFaces.push_back(ECellMDCodeT(*this,i,false));
        A_primaryFaces.push_back(ECellMDCodeT(*this,i,true));
      }
    }
  }
  template <typename P_Chain>
  void boundary(P_Chain& A_boundary) const{
    typedef typename P_Chain::ScalarType ScalarType;
    int sgn=ScalarType(1);
    for(unsigned int i=0;i<dim;++i){
      if(nonDegenerateAtCoord(i)){
        A_boundary.insert(std::make_pair(ECellMDCodeT(*this,i,false),-sgn));  // left face with -sgn
        A_boundary.insert(std::make_pair(ECellMDCodeT(*this,i,true),sgn));    // right face with sgn
        sgn=-sgn;
      }
    }
  }
  template <typename P_Chain>
  void coBoundary(P_Chain& A_coBoundary) const{
    typedef typename P_Chain::ScalarType ScalarType;
    int sgn=ScalarType(1);
    for(unsigned int i=0;i<dim;++i){
      if(nonDegenerateAtCoord(i)){ // in the nondegenerate dimensions we only change sign
        sgn=-sgn;
      }else{ // in the degenerate dimensions we construct cofaces and signs are reverse as in the case of boundary
        A_coBoundary.insert(std::make_pair(ECellMDCodeT(*this,false,i),sgn)); // left face with sgn
        A_coBoundary.insert(std::make_pair(ECellMDCodeT(*this,true,i),-sgn)); // right face with -sgn
      }
    }
  }
  friend bool operator==(const ECellMDCodeT A_a,const ECellMDCodeT A_b){
    return A_a.m_code==A_b.m_code;
  }
  friend bool operator!=(const ECellMDCodeT A_a,const ECellMDCodeT A_b){
    return A_a.m_code!=A_b.m_code;
  }

  friend std::istream& operator>> <cluster,dim>(std::istream& inp,ECellMDCodeT<cluster,dim>& A_cu);
//  friend std::ostream& operator<< <cluster,dim>(std::ostream& out,const ECellMDCodeT<cluster,dim,P_Scalar>& A_cu);

private:
  cluster m_code;
};// ********** class ECellMDCodeT ********** //

// -------------------------------------------------------------------------------------- //

template<typename cluster,int dim>
inline std::ostream& operator<<(std::ostream& out,const ECellMDCodeT<cluster,dim>& A_cu){
  for(unsigned int i=0;i<dim;++i){
    int j=A_cu.getValAtCoord(i);
    int k=j/2;
    if(i) out << "x";
    if(j % 2){
      out << "(" << k << "," << k+1 << ")";
    }else{
      out << "[" << k << "]";
    }
  }
  return out;
}

// -------------------------------------------------------------------------------------- //

template<typename cluster,int dim>
inline std::istream& operator>>(std::istream& inp,ECellMDCodeT<cluster,dim>& A_cu){
  ElementaryCell ec;
  inp >> ec;
  A_cu.m_code=ec.coords()[dim-1];
  for(int i=dim-2;i>=0;--i){
    (A_cu.m_code <<= ECellMDCodeT<cluster,dim>::bitsPerDimension) |= ec.coords()[i];
  }
  return inp;
}

// -------------------------------------------------------------------------------------- //

#endif //_ECELLMDCODE_H_
/// @}

