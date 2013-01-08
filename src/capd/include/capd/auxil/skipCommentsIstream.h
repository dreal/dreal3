/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file skipCommentsIstream.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_SKIP_COMMENTS_ISTREAM_H_)
#define _SKIP_COMMENTS_ISTREAM_H_

#include <istream>

class SkipCommentsIstream;

SkipCommentsIstream& operator>>(SkipCommentsIstream& A_in,char& A_c);

template<typename T>
SkipCommentsIstream& operator>>(SkipCommentsIstream& A_in,T& A_t);

class SkipCommentsIstream : public std::istream{
  std::istream& istrm;
public:
  SkipCommentsIstream(std::istream& A_is):istrm(A_is){}

  bool eof(){ return istrm.eof();}
  SkipCommentsIstream& get(char& A_c){ istrm.get(A_c); return *this;}
  SkipCommentsIstream& get(char* A_c,std::streamsize n){ istrm.get(A_c,n); return *this;}
  SkipCommentsIstream& unget(){ istrm.unget(); return *this;}
  void clear(){ istrm.clear();}
  std::ios::pos_type tellg(){return istrm.tellg();}
  void seekg(std::ios::pos_type p){istrm.seekg(p);}

  friend bool getline(SkipCommentsIstream& A_in,std::string& s){
    return std::getline(A_in.istrm,s);
  }

  template<typename T>
  friend SkipCommentsIstream& operator>>(SkipCommentsIstream& A_in,T& A_t);

  friend SkipCommentsIstream& operator>>(SkipCommentsIstream& A_in,char& A_c);
};

template<typename T>
SkipCommentsIstream& operator>>(SkipCommentsIstream& A_in,T& A_t){
  A_in.istrm >> A_t;
  return A_in;
}



#endif //_SKIP_COMMENTS_ISTREAM_H_

/// @}
