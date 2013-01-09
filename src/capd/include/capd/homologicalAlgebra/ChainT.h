/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ChainT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#if !defined(_CHAINT_H_)
#define _CHAINT_H_
#include <map>
#include <iostream>
#include "capd/bitSet/EuclBitSetT.h"

template<class ChainContainer>
class ChainT : public ChainContainer{
  public:

  typedef typename ChainContainer::key_type GeneratorCodeType;
  typedef typename ChainContainer::mapped_type ScalarType;
  typedef typename ChainContainer::iterator iterator;
  typedef typename ChainContainer::const_iterator const_iterator;

  ChainT(){}

  ChainT(const GeneratorCodeType& A_gen){
    this->insert(std::make_pair(A_gen,ScalarType(1)));
  }

  template<class OtherChainType>
  ChainT(const OtherChainType& A_otherChain){
    typename OtherChainType::const_iterator it;
    for(it=A_otherChain.begin();it!=A_otherChain.end();++it){
      typedef typename OtherChainType::GeneratorCodeType OtherGeneratorCodeType;
      typedef typename OtherChainType::ScalarType OtherScalarType;
      const OtherGeneratorCodeType& arg=it->first;
      const OtherScalarType& val=it->second;
      this->insert(std::make_pair(GeneratorCodeType(arg),ScalarType(val)));
    }
  }

  template <typename P_BitSet,int dim>
  void fillWith(const EuclBitSetT<P_BitSet,dim>& A_set){
    typename EuclBitSetT<P_BitSet,dim>::PointCoordIterator it(A_set);
    for(it=A_set.begin();it!=A_set.end();++it){
      this->insert(std::make_pair(GeneratorCodeType(it.coords(),1),ScalarType(1)));
    }
  }

  int ownDim(){
    if(this->empty()) return -1;
    else return this->begin()->first.ownDim();
  }

  bool nonZeroAt(const GeneratorCodeType& gen) const{
    return count(gen);
  }

  ScalarType at(const GeneratorCodeType& A_g) const{
    const_iterator it=this->find(A_g);
    if(it!=this->end()) return it->second;
    else return ScalarType(0);
  }

  ScalarType& accessAt(const GeneratorCodeType& A_g){
    return (*this)[A_g];
  }

  ChainT& operator+=(const ChainT& A_chain2){
    for(const_iterator it=A_chain2.begin();it!=A_chain2.end();++it){
      const GeneratorCodeType& arg=it->first;
      const ScalarType& val=it->second;
      (*this)[arg]+=val;
      if((*this)[arg]==ScalarType(0)){
        erase(arg);
      }
    }
    return *this;
  }

  ChainT& addMultiplicity(const ChainT& A_chain2, ScalarType s){
    for(const_iterator it=A_chain2.begin();it!=A_chain2.end();++it){
      const GeneratorCodeType& arg=it->first;
      const ScalarType& val=it->second;
      (*this)[arg]+= s*val;
      if((*this)[arg]==ScalarType(0)){
        erase(arg);
      }
    }
    return *this;
  }

  ChainT& operator-=(const ChainT& A_chain2){
    for(const_iterator it=A_chain2.begin();it!=A_chain2.end();++it){
      const GeneratorCodeType& arg=it->first;
      const ScalarType& val=it->second;
      (*this)[arg]-=val;
      if((*this)[arg]==ScalarType(0)){
        erase(arg);
      }
    }
    return *this;
  }

  ChainT& operator*=(const ScalarType& A_scalar){
    for(iterator it=this->begin();it!=this->end();++it){
      ScalarType& val=it->second;
      val*=A_scalar;
      if(val==ScalarType(0)){
        erase(it->first);
      }
    }
    return *this;
  }

  bool isZero(){
    if(this->size()==0) return true;
    for(iterator it=this->begin();it!=this->end();++it){
      if(it->second!=ScalarType(0)){
        return false;
      }
    }
    return true;
  }

  bool isSimple(){
    return (this->size()==1 && (this->begin()->second == ScalarType(1) || this->begin()->second == ScalarType(-1)));
  }
  void swap(ChainT& c2){
    this->ChainContainer::swap(c2);
  }
};

/************************************************************************************/

template<class ChainContainer>
inline std::ostream& operator<<(std::ostream& out,const  ChainT<ChainContainer>& A_chain){
  typedef typename ChainT<ChainContainer>::const_iterator const_iterator;

  out << "\r{";
  for(const_iterator it=A_chain.begin();it!=A_chain.end();++it){
    if(it!=A_chain.begin()) out << ",";
    out << "\n  " << it->first << "  ->  " << it->second;
  }
  if( A_chain.begin()!=A_chain.end() ) out << "\n";
  out << "}";
  return out;
}

// -------------------------------------------------------------------------------------- //
// Scalar product

template<typename ChainContainer>
inline typename ChainT<ChainContainer>::ScalarType operator*(const ChainT<ChainContainer>& A_chain1,const ChainT<ChainContainer>& A_chain2){
  typedef typename ChainT<ChainContainer>::const_iterator const_iterator;
  typedef typename ChainT<ChainContainer>::ScalarType ScalarType;

  ScalarType result(0);
  for(const_iterator it=A_chain1.begin();it!=A_chain1.end();++it){ // for each key with nonzero value
    result+=it->second*A_chain2.at(it->first);                     // equivalent to A_chain1[key]*A_chain2[key]
  }
  return result;
}

// -------------------------------------------------------------------------------------- //
// Product by a scalar

template<class ChainContainer>
inline ChainT<ChainContainer> operator*(typename ChainT<ChainContainer>::ScalarType A_s,const ChainT<ChainContainer>& A_chain){
  typedef typename ChainT<ChainContainer>::const_iterator const_iterator;
  typedef typename ChainT<ChainContainer>::ScalarType ScalarType;

  ChainT<ChainContainer> result;
  if(A_s != ScalarType(0)){
    for(const_iterator it=A_chain.begin();it!=A_chain.end();++it){
      result.insert(std::make_pair(it->first,it->second*A_s));
    }
  }
  return result;
}

// -------------------------------------------------------------------------------------- //


#endif //_CHAINT_H_
/// @}

