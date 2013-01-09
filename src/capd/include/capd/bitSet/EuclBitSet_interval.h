/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_interval.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(EUCLBITSETT_INTERVAL_H_)
#define EUCLBITSETT_INTERVAL_H_

template <typename word, int dim>
class EuclBitSetT<word,dim>::interval{
  int left,right;
public:
  interval():left(0),right(0){}
  interval(int a):left(a),right(a){}
  interval(int a,int b):left(a),right(b){}

  interval& operator*=(interval iv2){
    left=std::max(left,iv2.left);
    right=std::min(right,iv2.right);
    return *this;
  }

  bool empty(){
    return left>right;
  }
};
#endif //EUCLBITSETT_INTERVAL_H_
/// @}

