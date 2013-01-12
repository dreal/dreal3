/*                                                                           
**  fi_lib++  --- A fast interval library (Version 2.0)                     
**                                                                  
**  Copyright (C) 2001:                                                        
**                                                     
**  Werner Hofschuster, Walter Kraemer                               
**  Wissenschaftliches Rechnen/Softwaretechnologie (WRSWT)  
**  Universitaet Wuppertal, Germany                                           
**  Michael Lerch, German Tischler, Juergen Wolff von Gudenberg       
**  Institut fuer Informatik                                         
**  Universitaet Wuerzburg, Germany                                           
** 
**  This library is free software; you can redistribute it and/or
**  modify it under the terms of the GNU Library General Public
**  License as published by the Free Software Foundation; either
**  version 2 of the License, or (at your option) any later version.
**
**  This library is distributed in the hope that it will be useful,
**  but WITHOUT ANY WARRANTY; without even the implied warranty of
**  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
**  Library General Public License for more details.
**
**  You should have received a copy of the GNU Library General Public
**  License along with this library; if not, write to the Free
**  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
*/
#ifndef _XINTERVAL_H
#define _XINTERVAL_H

#include "ieee/primitive.hpp"

using filib::primitive;

//namespace xinewton
//{

// forward declarations for KCC :-( 
template <class T> 
class Xinterval;

template <class T>
Xinterval<T> operator %(T, T);

template <class T>
Xinterval<T> operator -(double, Xinterval<T>);

 

enum XIKindType {xiFinite, xiPlusInfty, xiMinusInfty, xiDouble, xiEmpty};

template <class I>
class Xinterval {                  
public: 
  XIKindType  kind;                
  double    inf, sup;

  Xinterval()
    : kind(xiFinite), inf(0.0), sup(0.0)
  {
  }
  
  Xinterval(XIKindType k, double x, double y)
    : kind(k), inf(x), sup(y)
  {
  }
  
  friend Xinterval operator%<> (I A, I B);
  friend Xinterval operator-<> (double a, Xinterval B );
};


//----------------------------------------------------------------------------
// Extended interval division 'A / B' where 0 in 'B' is allowed.
//----------------------------------------------------------------------------

template <class interval>
inline
Xinterval<interval> operator% (interval A, interval B)
{
  interval  c;
  Xinterval<interval> Q;

  if ( in(0.0, B) ) {
    if ( in(0.0, A) ) {
      Q.kind = xiDouble;                  // Q = [-oo,+oo] = [-oo,0] v [0,+oo]
      Q.sup  = 0.0;                       //----------------------------------
      Q.inf  = 0.0;
    }
    else if ( B == interval(0.0) ) {                                          // Q = [/]
      Q.kind = xiPlusInfty;                                         //--------
      Q.inf  = primitive::pred(sup(A)/inf(B));
    }
    else if ( (sup(A) < 0.0) && (sup(B) == 0.0) ) {         // Q = [Q.inf,+oo]
      Q.kind = xiPlusInfty;                                 //----------------
      Q.inf  = primitive::pred(sup(A)/inf(B));
    }
    else if ( (sup(A) < 0.0) && (inf(B) < 0.0) && (sup(B) > 0.0) ) {
      Q.kind = xiDouble;                      // Q = [-oo,Q.sup] v [Q.inf,+oo]
      Q.sup  = primitive::succ(sup(A)/sup(B));   //------------------------------
      Q.inf  = primitive::pred(sup(A)/inf(B));
    }
    else if ( (sup(A) < 0.0) && (inf(B) == 0.0) ) {         // Q = [-oo,Q.sup]
      Q.kind = xiMinusInfty;                                //----------------
      Q.sup  = primitive::succ(sup(A)/sup(B));
    }
    else if ( (inf(A) > 0.0) && (sup(B) == 0.0) ) {         // Q = [-oo,Q.sup]
      Q.kind = xiMinusInfty;                                //----------------
      Q.sup  = primitive::succ(inf(A)/inf(B));
    }
    else if ( (inf(A) > 0.0) && (inf(B) < 0.0) && (sup(B) > 0.0) ) {
      Q.kind = xiDouble;                      // Q = [-oo,Q.sup] v [Q.inf,+oo]
      Q.sup  = primitive::succ(inf(A)/inf(B));   //------------------------------
      Q.inf  = primitive::pred(inf(A)/sup(B));
    }
    else { // if ( (Inf(A) > 0.0) && (Inf(B) == 0.0) )
      Q.kind = xiPlusInfty;                                 // Q = [Q.inf,+oo]
      Q.inf  = primitive::pred(inf(A)/sup(B));                 //----------------
    }
  } // in(0.0,B)
  else {  // !in(0.0,B)
    c = A / B;                                            // Q = [C.inf,C.sup]
    Q.kind = xiFinite;                                    //------------------
    Q.inf  = inf(c);
    Q.sup  = sup(c);
  }

  return Q;
} 

//----------------------------------------------------------------------------
// Subtraction of an extended interval 'B' from a double value 'a'.
//----------------------------------------------------------------------------

template <class interval>
inline
Xinterval<interval> operator- (double a, Xinterval<interval> B)
{
  Xinterval<interval> D;

  switch (B.kind) {
    case xiFinite   : D.kind = xiFinite;                  // D = [D.inf,D.sup]
                      D.inf  = primitive::pred(a-B.sup);     //------------------
                      D.sup  = primitive::succ(a-B.inf);
                      break;
    case xiPlusInfty: D.kind = xiMinusInfty;                  // D = [inf,+oo]
                      D.sup  = primitive::succ(a-B.inf);         //--------------
                      break;
    case xiMinusInfty:D.kind = xiPlusInfty;                   // D = [-oo,sup]
                      D.inf  = primitive::pred(a-B.sup);         //--------------
                      break;
    case xiDouble    :D.kind = xiDouble;       // D = [-oo,D.sup] v [D.inf,+oo]
                      D.inf  = primitive::pred(a-B.sup);//------------------------
                      D.sup  = primitive::succ(a-B.inf);
                      if (D.inf < D.sup) D.inf = D.sup;
                      break;
    case xiEmpty    : D.kind = xiEmpty;                             // D = [/]
                      D.inf  = primitive::pred(a-B.sup);               //--------
                      break;
  } // switch
  return D;
}

//----------------------------------------------------------------------------
// Intersection of an interval 'X' and an extended interval 'Y'. The result
// is given as a pair of intervals V1 and V2, where one or both of them can 
// be empty intervals. The kind of the result is indicated by the return value
// of extIntersect:
//
// - eiSingleinterval: V1 is the result of the intersection, V2 is empty
// - eiDoubleinterval: both V1 and V2 are not empty
// - eiEmptyinterval:  the intersection is empty
//
// Note: 'empty intervals' are not produced explicitly. 
//----------------------------------------------------------------------------

enum ExtIntersectInfo {eiSingleinterval, eiDoubleinterval, eiEmptyinterval};

template <class interval>
inline
ExtIntersectInfo extIntersect(interval X, Xinterval<interval> Y, 
			      interval &V1, interval &V2)
{
  interval H;
  
  ExtIntersectInfo info = eiEmptyinterval;
  
  switch (Y.kind) {
     case xiFinite   : // [X.inf,X.sup] & [Y.inf,Y.sup]
                       //------------------------------
                       H = interval(Y.inf,Y.sup);
                       if ( !disjoint(X,H) ) {
			 V1 = intersect(X, H);
			 info = eiSingleinterval;
		       }
		       break;
    case xiPlusInfty: // [X.inf,X.sup] & [Y.inf,+oo]
                      //----------------------------
                      if (sup(X) >= Y.inf) {
                        if (inf(X) > Y.inf)
                          V1 = X;
                        else
                          V1 = interval(Y.inf,sup(X));
			info = eiSingleinterval;
		      }
                      break;
    case xiMinusInfty:// [X.inf,X.sup] & [-oo,Y.sup]
                      //----------------------------
                      if (Y.sup >= inf(X)) {
                        if (sup(X)<Y.sup)
                          V1 = X;
                        else
                          V1 = interval(inf(X),Y.sup);
			info = eiSingleinterval;
		      }
                      break;
    case xiDouble   : if ( (inf(X) <= Y.sup) && (Y.inf <= sup(X)) ) {
                        V1 = interval(inf(X),Y.sup);    // X & [-oo,Y.sup]
                        V2 = interval(Y.inf,sup(X));    // X & [Y.inf,+oo]
			info = eiDoubleinterval;
                      }
                      else if (Y.inf <= sup(X)){ // [X.inf,X.sup] & [Y.inf,+oo]
                        if (inf(X) >= Y.inf)     //----------------------------
                          V1 = X;
                        else
                          V1 = interval(Y.inf,sup(X));
			info = eiSingleinterval;
		      }
                      else if (inf(X) <= Y.sup){// [X.inf,X.sup] & [-oo,Y.sup]
                        if (sup(X) <= Y.sup)    //----------------------------
                          V1 = X;
                        else
			  V1 = interval(inf(X),Y.sup);
			info = eiSingleinterval;
		      }
                      break;
    case xiEmpty    : break;                           // [X.inf,X.sup] ** [/]
  } // switch                                          //---------------------

  return info;
}


//}

#endif




