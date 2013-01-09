/////////////////////////////////////////////////////////////////////////////
/// @addtogroup Interval
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file mpIntervalFun.c
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include <exception>

namespace capd{
namespace multiPrec{
   
class NaNException: public std::exception{
   const char * what() const throw ()
   {
      return "Not a number. ";
   }
};



/* returns in quad the integer part of the division of x by Pi/2        */
/* the result is exact                                                  */
/* the returned value is the precision required to perform the division */


Interval::BoundType quadrant(const Interval::BoundType &x)
{
  int ok = 0;
  PrecisionType defPrec = x.getDefaultPrecision(), 
                prec = x.getPrecision(),
                precIncreaseRate = 64;
  Interval  twoOverPi, tmp;
  Interval::BoundType quad = 0.0;
            
  if(!(x==0))
  {
     do{
        x.setDefaultPrecision(prec);
        twoOverPi = Interval(2) / Interval::Pi();
        tmp = twoOverPi * x;
        ok = compare(floor(tmp.leftBound()), floor(tmp.rightBound()));
  
        if( ok != 0 )
           prec += precIncreaseRate;
           
     }while(ok != 0);
     
     quad = floor(tmp.leftBound());
     Interval::BoundType::setDefaultPrecision(defPrec);
  }
  return quad;
}




 
Interval sin(const Interval& x)
{
  Interval::BoundType quad_left, quad_right;
  Interval::BoundType left, right;
  
  int ql_mod4, qr_mod4;

  if (isnan(x)) 
    throw NaNException();

  if (isinf(x)) {
    /* the two endpoints are the same infinite */
    if ( compare(x.leftBound(), x.rightBound()) == 0) 
       throw NaNException();
   
    return Interval(-1.0, 1.0);
  }
   

  /* quad_left gives the quadrant where the left endpoint of b is */
  /* quad_left = floor(2 b->left / pi)                            */
  /* idem for quad_right and b->right                             */
  
  quad_left = quadrant(x.leftBound());
  quad_right = quadrant(x.rightBound());


  if (quad_right - quad_left >= 4.0) 
  {
     return Interval (-1, 1);
  } else {
  /* there is less than one period in b */
  /* let us discuss according to the position (quadrant) of the endpoints of b    */
  
    /* qr_mod4 gives the quadrant where the right endpoint of b is */
    /* qr_mod4 = floor(2 b->right / pi) mod 4 */
    
    qr_mod4 = toInt(quad_right) % 4; // Warning: It do not work for huge numbers (greather than long int)
  
    /* quad_left gives the quadrant where the left endpoint of b is */
    /* quad_left = floor(2 b->left / pi) mod 4 */
    ql_mod4 = toInt(quad_left) % 4;  // Warning: It do not work for huge numbers (greather than long int)
    
    switch (qr_mod4) {
      case 0:
        switch (ql_mod4) {
          case 0:
          case 3:
            roundDown();
            left = sin(x.leftBound());
            roundUp();
            right = sin(x.rightBound());  
            break;
                    
          case 1:
            roundUp();
            left = sin(x.leftBound());
            right = sin(x.rightBound());  
            if(right < left) 
               right = left;
            left = Interval::BoundType(-1.0, RoundDown);
            break;
          case 2:
            roundUp();
            right = sin(x.rightBound());  
            left = Interval::BoundType(-1.0, RoundDown);
            break;
        } // gr_mod4 =  0:
        break;
      case 1:
        switch (ql_mod4) {
          case 0:
            roundDown();
            left = sin(x.leftBound());
            right = sin(x.rightBound());  
            if(right < left) 
               left = right;
            right = Interval::BoundType(1.0, RoundUp);
            break;
            
          case 1:
            roundDown();
            left = sin(x.rightBound());
            roundUp();
            right = sin(x.leftBound());  
            break;
            
          case 2:
            right = Interval::BoundType(1.0, RoundUp);
            left = Interval::BoundType(-1.0, RoundDown); 
            break;
            
          case 3:
            roundDown();
            left = sin(x.leftBound());
            right = Interval::BoundType(1.0, RoundUp);
            break;
        }// gr_mod4 =  1:
        break;
      case 2:
        switch (ql_mod4) {
          case 0:
            roundDown();
            left =  sin(x.rightBound());  
            right = Interval::BoundType(1.0, RoundUp);
            break;
          
          case 1:
          case 2:
            roundDown();
            left = sin(x.rightBound());
            roundUp();
            right = sin(x.leftBound());  
            break;
          
          case 3:
            roundDown();
            left = sin(x.leftBound());
            right = sin(x.rightBound());  
            if(right < left) 
               left = right;
            right = Interval::BoundType(1.0, RoundUp);
            break;
        }// gr_mod4 =  2:
        break;
      case 3:
        switch (ql_mod4) {
          case 0:
            right = Interval::BoundType(1.0, RoundUp);
            left = Interval::BoundType(-1.0, RoundDown); 
            break;
            
          case 1:
            roundUp();
            right = sin(x.leftBound());  
            left = Interval::BoundType(-1.0, RoundDown);
            break;
            
          case 2:
            roundUp();
            left = sin(x.leftBound());
            right = sin(x.rightBound());  
            if(right < left) 
               right = left;
            left = Interval::BoundType(-1.0, RoundDown);
            break;
            
          case 3:
            roundDown();
            left = sin(x.leftBound());
            roundUp();
            right = sin(x.rightBound());  
            break;
            
        } // gr_mod4 =  3:
        break;
      } // switch(gr_mod4)
  } 
  return Interval(left, right);
} // sin


 
Interval cos(const Interval& x)
{
  Interval::BoundType quad_left, quad_right;
  Interval::BoundType left, right;
  
  int ql_mod4, qr_mod4;

  if (isnan(x)) 
    throw NaNException();

  if (isinf(x)) {
    /* the two endpoints are the same infinite */
    if ( compare(x.leftBound(), x.rightBound()) == 0) 
       throw NaNException();
   
    return Interval(-1.0, 1.0);
  }
   

  /* quad_left gives the quadrant where the left endpoint of b is */
  /* quad_left = floor(2 b->left / pi)                            */
  /* idem for quad_right and b->right                             */
  
  quad_left = quadrant(x.leftBound());
  quad_right = quadrant(x.rightBound());


  if (quad_right - quad_left >= 4.0) 
  {
     return Interval (-1, 1);
  } else {
  /* there is less than one period in b */
  /* let us discuss according to the position (quadrant) of the endpoints of b    */
  
    /* qr_mod4 gives the quadrant where the right endpoint of b is */
    /* qr_mod4 = floor(2 b->right / pi) mod 4 */
    
    qr_mod4 = toInt(quad_right) % 4; // Warning: It do not work for huge numbers
  
    /* quad_left gives the quadrant where the left endpoint of b is */
    /* quad_left = floor(2 b->left / pi) mod 4 */
    ql_mod4 = toInt(quad_left) % 4;
               
    switch (qr_mod4) {
      case 0:
        switch (ql_mod4) {
            
          case 0:
            roundDown();
            left = cos(x.rightBound());
            roundUp();
            right = cos(x.leftBound());  
            break;
            
          case 1:
            right = Interval::BoundType(1.0, RoundUp);
            left = Interval::BoundType(-1.0, RoundDown); 
            break;
            
          case 2:
            roundDown();
            left = cos(x.leftBound());
            right = Interval::BoundType(1.0, RoundUp);
            break;
          
          case 3:
            roundDown();
            left = cos(x.leftBound());
            right = cos(x.rightBound());  
            if(right < left) 
               left = right;
            right = Interval::BoundType(1.0, RoundUp);
            break;
          
        }
        break;
      case 1:
        switch (ql_mod4) {
          case 3:
            roundDown();
            left =  cos(x.rightBound());  
            right = Interval::BoundType(1.0, RoundUp);
            break;
          
          case 0:
          case 1:
            roundDown();
            left = cos(x.rightBound());
            roundUp();
            right = cos(x.leftBound());  
            break;
          
          case 2:
            roundDown();
            left = cos(x.leftBound());
            right = cos(x.rightBound());  
            if(right < left) 
               left = right;
            right = Interval::BoundType(1.0, RoundUp);
            break;
        }
        break;
      case 2:
        switch (ql_mod4) {
            
          case 0:
            roundUp();
            right = cos(x.leftBound());  
            left = Interval::BoundType(-1.0, RoundDown);
            break;
            
          case 1:
            roundUp();
            left = cos(x.leftBound());
            right = cos(x.rightBound());  
            if(right < left) 
               right = left;
            left = Interval::BoundType(-1.0, RoundDown);
            break;
            
          case 2:
            roundDown();
            left = cos(x.leftBound());
            roundUp();
            right = cos(x.rightBound());  
            break;
        
          case 3:
            right = Interval::BoundType(1.0, RoundUp);
            left = Interval::BoundType(-1.0, RoundDown); 
            break;
            
        }
        break;
        
        case 3:
        switch (ql_mod4) {
                    
          case 0:
            roundUp();
            left = cos(x.leftBound());
            right = cos(x.rightBound());  
            if(right < left) 
               right = left;
            left = Interval::BoundType(-1.0, RoundDown);
            break;
            
          case 1:
            roundUp();
            right = cos(x.rightBound());  
            left = Interval::BoundType(-1.0, RoundDown);
            break;
            
          case 2:
          case 3:
            roundDown();
            left = cos(x.leftBound());
            roundUp();
            right = cos(x.rightBound());  
            break;
        }
        break;
      }
  }
  return Interval(left, right);
}  // cos

 
Interval tan(const Interval& x)
{
  
  if (isnan(x)) 
    throw NaNException();

  if (isinf(x)) {
    /* the two endpoints are the same infinite */
    if ( compare(x.leftBound(), x.rightBound()) == 0) 
       throw NaNException();
   
    return Interval(Interval::BoundType::NegativeInfinity(), Interval::BoundType::PositiveInfinity());
  }
   
  Interval::BoundType quad_left = quadrant(x.leftBound()),
             quad_right = quadrant(x.rightBound());

  long int qr_mod2 = toInt(quad_right) % 2, // Warning: It do not work for huge numbers
           ql_mod2 = toInt(quad_left) % 2;
  
  /* if there is at least one period in b or if b contains a Pi/2 + k*Pi, */
  /* then a = ]-oo, +oo[ */ 
  if ((quad_right - quad_left >= 2.0)||((ql_mod2==0)&&(qr_mod2==1))) 
     return Interval(Interval::BoundType::NegativeInfinity(), Interval::BoundType::PositiveInfinity());

  /* within one period, tan is increasing */   
  Interval::BoundType left, right;
  roundDown();
  left = tan(x.leftBound());
  roundUp();
  right = tan(x.rightBound());
  return Interval(left, right);
}  //tan


 
Interval cot(const Interval& x)
{
  return cos(x) / sin(x);
}



 
Interval log(const Interval& x)
{
  Interval res;
  roundDown();
  res.left=log(x.leftBound());
  roundUp();
  res.right=log(x.rightBound());
  if (isnan(res)) 
    throw NaNException();
  return res;
}


 
Interval exp(const Interval& x)
{
  Interval res;
  roundDown();
  res.left=exp(x.leftBound());
  roundUp();
  res.right=exp(x.rightBound());
  if (isnan(res)) 
    throw NaNException();
  return res;
}

//-------- sqrt -----------------
 
Interval sqrt(const Interval  & z)
{
  Interval::BoundType  left, right;

  if(z.leftBound()<0.0){
     throw intervalError("Interval Function sqrt(x) - domain error",z.left,z.right);
  }

  roundUp();
  right=sqrt(z.right);

  roundDown();
  left=sqrt(z.left);

 return Interval(left, right);
}//-------------------------------


 
Interval power(const Interval &a, const Interval &b)
{
 if( a.leftBound() < 0 )
 {
  throw std::range_error("power(A, B): interval A must be greater than zero\n");
 }
 return exp(b * log(a));
}

 
Interval power(const Interval& value, long  int exponent)
//   value^{exponent}
{
   Interval out(1.0);  // when   exponent==0
   Interval::BoundType l,r,t;
  // int prev_exp=exponent;
   int sign=1;

   if (exponent < 0 ) {
     sign=0;
     exponent = -exponent;
   }


   l=value.leftBound();
   r=value.rightBound();

   /* if 'exponent' is even, then we need to correct the ends of interval -
     only absolute values matter*/
   if (exponent % 2 == 0){

     l = abs(l);
     r = abs(r);

     if (l > r) {
       t=r;
       r=l;
       l=t;
     }

     if (in(0.0,value)) l=0.0;
   }

   
    roundUp();
    out.right = r.pow(exponent); 
    roundDown();
    out.left = l.pow(exponent);
   if(sign==0)  // when an exponent is negative
   {
     out = Interval(1.0)/out;
   }

   return out;

}//--------------------------------------------------------------------

//------------------------ Interval hyperbolic functions
//----------------------------- sinh, cosh, tanh, coth
 
Interval  cosh(const Interval &x)
{
  return ( (exp(x)+exp(-x))/2 );
}

 
Interval  sinh(const Interval &x)
{
  return ( (exp(x)-exp(-x))/2 );
}

 
Interval  tanh(const Interval &x)
{
  return ( (exp(x)-exp(-x))/(exp(x)+exp(-x)) );
}

 
Interval  coth(const Interval &x)
{
  return ( (exp(x)+exp(-x))/(exp(x)-exp(-x)) );
}


//--------------------------------------------------------------------

Interval  Interval::Pi( PrecisionType prec /*= 0*/)
{
   if(prec == 0) 
      prec = BoundType::getDefaultPrecision();
   return Interval(BoundType::Pi(RoundDown, prec), BoundType::Pi(RoundUp, prec));
}


Interval Interval::Log2( PrecisionType prec /*=0*/)
{
   if(prec == 0) 
      prec = BoundType::getDefaultPrecision();
   return Interval(BoundType::Log2(RoundDown, prec), BoundType::Log2(RoundUp, prec));
}


Interval Interval::Euler( PrecisionType prec /*=0*/)
{
   if(prec == 0) 
      prec = BoundType::getDefaultPrecision();
   return Interval(BoundType::Euler(RoundDown, prec), BoundType::Euler(RoundUp, prec));
}


void splitInterval(Interval& i, Interval::BoundType & diam)
// On output:  i(input) \subset i(output) + [-diam + diam]
{
 Interval::BoundType l,r,s;
 l = i.left;
 r = i.right;
 s = (l+r)/2;
 i = Interval(s);
 roundUp();
 diam = r-s;
 r = s-l;
 if (diam<r)
   diam=r;
}

void Interval::split(Interval &r){
  Interval::BoundType xl,xr;
  xl=left;
  xr=right;
  roundNearest();
  left=right=(xl+xr)/2;
  roundDown();
  r.left=xl-left;
  roundUp();
  r.right=xr-right;
  #ifdef DEBUGGING
  if(r.left>r.right)
      throw intervalError(" split",r.left,r.right);
  #endif
}

Interval intervalHull(const Interval & i1, const Interval & i2)
// the function returns an interval containing i1 and i2
{
  Interval retval;
  retval.left=(i1.left < i2.left)? i1.left : i2.left;
  retval.right=(i1.right>i2.right)? i1.right: i2.right;
  return retval;

}

int  intersection(const Interval &x1, const Interval &x2, Interval &cp)
 // on output:  if common part of <x1> and <x2> is nonempty then
 //                cp =intersection of <x1> and <x2>
 //                 and 1 is returned
 //              otherwise 0 is returned and cp is untouched
{
  int nonempty;
  Interval::BoundType l=x1.leftBound();
  if(x2.leftBound() > l) l=x2.leftBound();
  Interval::BoundType r=x1.rightBound();
  if(x2.rightBound() < r) r=x2.rightBound();

  nonempty=(l<=r);
  if(nonempty)  
     cp=Interval(l,r);
  return(nonempty);
}

}}  // end of namespace capd::multiPrec

/// @}
