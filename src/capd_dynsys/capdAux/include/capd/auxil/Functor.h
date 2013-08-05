/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Functor.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_FUNCTOR_H_)
#define _FUNCTOR_H_

namespace capd {
  namespace auxil {

template<class Op2, class Op1>
class ComposedFunctor{
  Op1 op1;
  Op2 op2;
  public:
  ComposedFunctor(const Op2& A_op2, const Op1& A_op1):op1(A_op1),op2(A_op2){}
  typedef typename Op1::argumentType argumentType;
  typedef typename Op2::valueType valueType;
  valueType operator()(argumentType A_a){
    return op2(op1(A_a));
  }
};

  // Do we need this? When it is in global namespace, then it is used for gmp numbers
template<class Op2, class Op1>
inline ComposedFunctor<Op2,Op1> operator*(const Op2& op2,const Op1& op1){
  return ComposedFunctor<Op2,Op1>(op2,op1);
}

template<typename valType,typename argType>
class Functor{

  public:
  typedef argType argumentType;
  typedef valType valueType;
  typedef valueType (*functionPtrType)(argumentType A_a);
  Functor(valueType (*A_fPtr)(argumentType)):functionPtr(A_fPtr){}
  valueType operator()(argumentType A_a){
    return (*functionPtr)(A_a);
  }
  private:
  valueType (*functionPtr)(argumentType A_a);
};

}
}

#endif //_FUNCTOR_H_
/// @}

