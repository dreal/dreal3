/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BitmapT.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#if !defined(_BITMAP_HPP_)
#define _BITMAP_HPP_
#include <vector>
#include "capd/bitSet/BitmapT.h"
#include "capd/auxil/stringOstream.h"
#include "capd/multiEngHom/powerTwoCeiling.h"

/************************************************************************************/

template <typename word>
void BitmapT<word>::setupBitmapMem(){
  bitmapEnd=bitmap=0;
  // It seems that
  if(baseTwoLog(length)+2>=8*sizeof(unsigned long int)){
      std::ostringstream s;
      s << "Requested bitmap length of " << length << " words exceeds the size of long (when counted in bytes)";
      throw std::runtime_error(s.str());
  }
  if(length){
  // -- MM  long int mem=memSize();    // *** DEBUG *** //
  // -- MM  std::cout << " BitmapT request for " << length << " before  memory available " << mem << std::endl; // *** DEBUG *** //
    try{
      bitmap=new word[length];
    }catch(std::bad_alloc& e){
      std::ostringstream s;
      s << "Memory request for bitmap of " << length*sizeof(word) << " bytes failed";
      throw std::runtime_error(s.str());
    }
    // -- MM  std::cout << "Bitmap of " << length << " bytes reseved" << std::endl; // *** DEBUG *** //
    // -- MM  mem=memSize();                                                 // *** DEBUG *** //
    // -- MM  std::cout << " BitmapT after  memory available " << mem << std::endl; // *** DEBUG *** //
  }

  bitmapEnd=bitmap+length;
}

/************************************************************************************/

template <typename word>
BitmapT<word>::BitmapT(int A_wordLength,bool A_clear):length(A_wordLength){
  setupBitmapMem();
  if (A_clear) clear();
}

/************************************************************************************/

// BitmapT from a provided bitmap data
template <typename word>
BitmapT<word>::BitmapT(int A_wordLength, const char* bytes):length(A_wordLength){
  bitmap=reinterpret_cast<word*>(const_cast<char*>(bytes));
  bitmapEnd=bitmap+length;
}

/************************************************************************************/

// BitmapT from a string
template <typename word>
BitmapT<word>::BitmapT(const std::string& s):length(0){

  setupBitmapMem();
  std::istringstream in(s);
  in >> *this;
}

/************************************************************************************/

template <typename word>
BitmapT<word>::BitmapT(const BitmapT& A_org,bool A_clear):length(A_org.length){
  setupBitmapMem();
  WordIterator itEnd=end();
  if (A_clear) clear();
  else for(WordIterator it=begin(),it2=A_org.begin();it<itEnd;++it,++it2) *it=*it2;
}

/************************************************************************************/

template <typename word>
BitmapT<word>& BitmapT<word>::invert(){
  WordIterator itEnd=end();
  for(WordIterator it=begin();it<itEnd;++it) *it=~(*it);
  return *this;
}

/************************************************************************************/

template <typename word>
BitmapT<word>& BitmapT<word>::clear(){
  WordIterator itEnd=end();
  for(WordIterator it=begin();it<itEnd;++it) *it=0;
  return *this;
}


/************************************************************************************/

template <typename word>
BitmapT<word>& BitmapT<word>::operator=(const BitmapT<word>& A_BitMap2){
  if(&A_BitMap2==this) return *this;
  length=A_BitMap2.length;
  if(bitmap) delete[] bitmap;
  setupBitmapMem();
  WordIterator itEnd=end();
  for(WordIterator it=begin(),it2=A_BitMap2.begin();it<itEnd;++it,++it2) *it=*it2;
  return *this;
}

/************************************************************************************/

template <typename word>
bool BitmapT<word>::operator==(const BitmapT<word>& set2){
  if(length!=set2.length) throw "Request to compare two bitmaps of different length\n";
  WordIterator p,q;
  for(p=begin(),q=set2.begin();p<end();++p,++q) if(*p!=*q) return false;
  return true;
}

/************************************************************************************/

template <typename word>
bool BitmapT<word>::operator<=(const BitmapT<word>& set2){
  if(length!=set2.length) throw "Request to compare two bitmaps of different length\n";
  WordIterator p,q;
  for(p=begin(),q=set2.begin();p<end();++p,++q) if((*p & *q) != *p) return false;
  return true;
}

/************************************************************************************/

template <typename word>
BitmapT<word>& BitmapT<word>::operator*=(const BitmapT<word>& set2){
  // temporary implementation!!
  // works only conditiionally!!
  if(length!=set2.length) throw "Request to multiply two bitmaps of different length\n";
  WordIterator p,q;
  for(p=begin(),q=set2.begin();p<end();++p,++q) *p&=*q;
  return *this;
}

/************************************************************************************/

template <typename word>
BitmapT<word>& BitmapT<word>::operator+=(const BitmapT<word>& set2){
  // temporary implementation!!
  // works only conditiionally!!
  if(length!=set2.length) throw "Request to add two bitmaps of different length\n";
  WordIterator p,q;
  for(p=begin(),q=set2.begin();p<end();++p,++q) *p|=*q;
  return *this;
}

/************************************************************************************/

template <typename word>
BitmapT<word>& BitmapT<word>::operator-=(const BitmapT<word>& set2){
  // temporary implementation!!
  // works only conditiionally!!
  if(length!=set2.length){
    std::string s;
    s << "Request to assign to a bitmap of different lengths: " << length << " and " << set2.length;
    throw std::runtime_error(s.c_str());
//    throw "Request to assign to a bitmap of different length\n";
  }
  WordIterator p,q;
  for(p=begin(),q=set2.begin();p<end();++p,++q) *p=(*p) & ~(*q);
  return *this;
}

/************************************************************************************/

template <typename word>
bool BitmapT<word>::empty() const{
  WordIterator p;
  for(p=begin();p<end();++p) if(*p) return false;
  return true;
}

/************************************************************************************/

// reverse the order of bits in words
template <typename word>
void BitmapT<word>::swapBits(){
  for(WordIterator it=begin();it<end();++it){
    word w=0;
    for(int i=0;i<bitsPerWord;++i){
      w = w | (((*it >> i) & 1) << (bitsPerWord-i-1));
    }
    *it=w;
  }
}

/************************************************************************************/

// reverse the order of bytes in words
template <typename word>
void BitmapT<word>::swapBytes(){
  if(sizeof(word)==1) return;
  for(WordIterator it=begin();it<end();++it){
    char* cPtr=reinterpret_cast<char*>(&(*it));
    char c=*cPtr;
    *cPtr=*(cPtr+sizeof(word)-1);
    *(cPtr+sizeof(word)-1)=c;
    if(sizeof(word)==4){
      c=*(cPtr+1);
      *(cPtr+1)=*(cPtr+2);
      *(cPtr+2)=c;
    }
  }
}

/************************************************************************************/
template <typename word>
std::istream& operator>>(std::istream& in,BitmapT<word>& A_BitMap){
 int bitsPerWord=8*sizeof(word);
 std::vector<bool> v;
 while(true){
    char c;
    in >> c;
    if(in.eof()) break;
    int a=c-'0';
    if(a<0 || a>1){
      std::ostringstream s;
      s << "Incorrect character '" << c << "' found when reading bitmap. It must be 0 or 1! \n";
      throw std::runtime_error(s.str());
    }
    v.push_back(bool(a));
  }
  int length=v.size()/bitsPerWord+(v.size()%bitsPerWord != 0);
  BitmapT<word> internal(length,true); // true=clear
  typename BitmapT<word>::BitIterator it(internal);
  unsigned int i;
  for(i=0,it=internal.begin();i<v.size();++it,++i){
    if(v[i]) it.setBit();
  }
  swap(A_BitMap,internal);
  return in;
}

/************************************************************************************/

template <typename word>
std::ostream& operator<<(std::ostream& out,const BitmapT<word>& A_BitMap){
  typename BitmapT<word>::BitIterator it(A_BitMap);
  int cnt=0;
  for(it=A_BitMap.begin();it<A_BitMap.end();++it,++cnt){
    if((cnt > 0) && ((cnt % 8) == 0)) out << " ";
    out << it.getBit();
  }
  return out;
}

/************************************************************************************/

#endif


/// @}

