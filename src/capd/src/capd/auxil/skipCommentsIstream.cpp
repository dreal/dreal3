/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file skipCommentsIstream.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#include "capd/auxil/skipCommentsIstream.h"
#include <iostream>


SkipCommentsIstream& operator>>(SkipCommentsIstream& A_in,char& A_c){
  A_in.istrm >> A_c;
  while(A_c == ';' || A_c == '#' || A_c == '%'){
    do{
      A_in.get(A_c);
    }while(A_c!='\n' && !A_in.eof() );
    if (!A_in.eof()) A_in.istrm >> A_c;
    else A_c=' ';
  }
  return A_in;
}




/// @}
