/////////////////////////////////////////////////////////////////////////////
/// @addtogroup Interval
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file mpIntervalOp.c
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

//--------------
//               header file of class 'Interval'
//--------------


namespace capd{
namespace multiPrec{
   
//---------          ASSIGMENTS   ---------------------------------------------------
//Operator=

Interval& Interval::operator =(const Interval& _inter)
{   if(this == &_inter)    // this a=a
       return *this;
    left  = _inter.left;
    right = _inter.right;
    return *this;
}

//Operator +=

Interval& Interval::operator +=(const Interval& _inter)
{   roundDown();
    left  += _inter.left;
    roundUp();
    right += _inter.right;
    #ifdef  DEBUGGING
    if(left>right)
      throw intervalError(" Operator += ",left,right);
    #endif
    return *this;
}

//Operator  -=

Interval& Interval::operator -=(const Interval& _inter)
{   roundDown();
    left  -= _inter.right;
    roundUp();
    right -= _inter.left;
    #ifdef  DEBUGGING
    if(left>right)
      throw intervalError(" Operator -= ",left,right);
    #endif
    return *this;
}

//Operator *=

Interval& Interval::operator *=(const Interval& _inter)
{

    if((right==0.0) && (left==0.0)) return *this;
    if ((_inter.right==0.0) && (_inter.left==0.0)){
      left=0.0;
      right=0.0;
      return *this;
    }


    if(right<=0 &&  _inter.right<=0)  // (--)(--)
    {   roundDown();
        Interval::BoundType temp=right*_inter.right;
        roundUp();
        right=left*_inter.left;
        left=temp;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator *= (--)(--)",left,right);
        #endif
        return *this;
    }


   if( right<=0 && _inter.left<=0 && _inter.right>=0) // (--)(-+)
    {   roundDown();
        Interval::BoundType temp=left*_inter.right;
        roundUp();
        right=left*_inter.left;
        left=temp;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator *= (--)(-+)",left,right);
        #endif
        return *this;
    }


    if(right<=0 && _inter.left>=0 ) // (--)(++)
    {   roundDown();
        left*=_inter.right;
        roundUp();
        right*=_inter.left;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator *= (--)(++)",left,right);
        #endif
        return *this;
    }

   if(left<=0 && right>=0 &&  _inter.right<=0) // (-+)(--)
    {   roundDown();
        Interval::BoundType temp=right*_inter.left;
        roundUp();
        right=left*_inter.left;
        left=temp;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator *= (-+)(--)",left,right);
        #endif
        return *this;
    }


   if(left<=0 && right>=0 && _inter.left<=0 && _inter.right>=0)  // (-+)(-+)
    {  roundDown();
       Interval::BoundType l1=left*_inter.right, l2=right*_inter.left;
       roundUp();
       Interval::BoundType r1=left*_inter.left, r2=right*_inter.right;
       if(l1>l2) left=l2;
       else left=l1;
       if(r1<r2) right=r2;
       else right=r1;
       #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator *= (-+)(-+)",left,right);
        #endif
       return *this;
    }



   if(left<=0 && right>=0 && _inter.left>=0 ) // (-+)(++)
    {   roundDown();
        left*=_inter.right;
        roundUp();
        right*=_inter.right;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator *= (-+)(++)",left,right);
        #endif
        return *this;
    }


    if(left>=0 &&  _inter.right<=0) // (++)(--)
    {   roundDown();
        Interval::BoundType temp=right*_inter.left;
        roundUp();
        right=left*_inter.right;
        left=temp;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator *= (++)(--)",left,right);
        #endif
        return *this;
    }

    if(left>=0  && _inter.left<=0 && _inter.right>=0) // (++)(-+)
    {   roundDown();
        left=right*_inter.left;
        roundUp();
        right*=_inter.right;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator *= (++)(-+)",left,right);
        #endif
        return *this;
    }


    if(left>=0 && _inter.right >=0){ // (++)(++)
      roundDown();
      left*=_inter.left;
      roundUp();
      right*=_inter.right;

      #ifdef  DEBUGGING
      if(left>right)
        throw intervalError(" Operator *= (++)(++)",left,right);
      #endif
      return *this;
    }


    throw intervalError("Error *** Fatal Interval error ", left, right);
  return *this;
}

//Operator  /=

Interval& Interval::operator /=(const Interval& _inter)
{
  if(_inter.left<=0 && _inter.right>=0)
    {
      throw intervalError("Error ***  Possible divide by zero.  /=", left, right);
    }


 if(right<=0 && _inter.right<0){  // (--)(--)
   roundDown();
   Interval::BoundType ll=right/_inter.left;

   roundUp();
   Interval::BoundType rr=left/_inter.right;
   left=ll;
   right=rr;
   #ifdef  DEBUGGING
    if(left>right)
      throw intervalError(" Operator /= (--)(--)",left,right);
    #endif
   return *this;
 }

 if(right<=0 && _inter.left>0)   // (--)(++)
    {   roundDown();
        left/=_inter.left;
        roundUp();
        right/=_inter.right;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator /= (--)(++)",left,right);
        #endif

        return *this;
    }


 if(left<=0 && right>=0 && _inter.right<0)  // (-+)(--)
    {   roundDown();
        Interval::BoundType temp=right/_inter.right;
        roundUp();
        right=left/_inter.right;
        left=temp;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator /= (-+)(--)",left,right);
        #endif
        return *this;
    }


 if(left<=0 && right>=0 && _inter.left>0)  // (-+)(++)
    {   roundDown();
        left /=_inter.left;
        roundUp();
        right/=_inter.left;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator /= (-+)(++)",left,right);
        #endif
        return *this;
    }

 if(left>=0 && _inter.right<0) // (++)(--)
    {   roundDown();
        Interval::BoundType temp=right/_inter.right;
        roundUp();
        right=left/_inter.left;
        left=temp;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator /= (++)(--)",left,right);
        #endif

        return *this;
    }

 if(left>=0 && _inter.left>0) // (++)(++)
    {   roundDown();
        left/=_inter.right;
        roundUp();
        right/=_inter.left;
        #ifdef  DEBUGGING
        if(left>right)
          throw intervalError(" Operator /= (++)(++)",left,right);
        #endif
        return *this;
    }

  throw intervalError("Error *** Fatal Interval error in  /= ",left,right);

  return *this;
}

//---------------------------------------------------------------------------------

// ---------------- Operator +    -------------------------------------------------

Interval operator +(const Interval& _inter1, const Interval & _inter2)
{ 
  Interval res;
  roundDown();
  res.left = _inter1.left+_inter2.left;
  roundUp();
  res.right = _inter1.right+_inter2.right;
  return res;
}

Interval operator+(const Interval& _inter, const Interval::BoundType &_val)
{  
  Interval res;
  roundDown();
  res.left = _inter.left+_val;
  roundUp();
  res.right = _inter.right+_val;
  return res;
}


Interval operator+(const Interval::BoundType &_val,const Interval & _inter)
{ 
  Interval res;
  roundDown();
  res.left = _inter.left+_val;
  roundUp();
  res.right = _inter.right+_val;
  return Interval(res.left, res.right);
}


Interval operator+(const Interval& _inter, double _val)
{  
  Interval res;
  roundDown();
  res.left = _inter.left+_val;
  roundUp();
  res.right = _inter.right+_val;
  return res;
}


Interval operator+(double _val,const Interval & _inter)
{ 
  Interval res;
  roundDown();
  res.left = _inter.left+_val;
  roundUp();
  res.right = _inter.right+_val;
  return Interval(res.left, res.right);
}
//--------------------------------------------------------------------

//---------   Operator  -      ----------------------------------------

Interval operator -(const Interval& _inter1, const Interval& _inter2)
{  
  Interval res;
  roundDown();
  res.left = _inter1.left-_inter2.right;
  roundUp();
  res.right = _inter1.right-_inter2.left;
  return res;
}


Interval operator-(const Interval& _inter, const Interval::BoundType& _val)
{  
  Interval res;
   roundDown();
   res.left = _inter.left-_val;
   roundUp();
   res.right = _inter.right-_val;
   return res;
}


Interval operator-(const Interval::BoundType& _val, const Interval& _inter)
{  
  Interval res;
  roundDown();
  res.left = _val-_inter.right;
  roundUp();
  res.right = _val-_inter.left;
  return res;
}

Interval operator-(const Interval& _inter, double _val)
{  
  Interval res;
   roundDown();
   res.left = _inter.left-_val;
   roundUp();
   res.right = _inter.right-_val;
   return res;
}


Interval operator-(double _val, const Interval& _inter)
{  
  Interval res;
  roundDown();
  res.left = _val-_inter.right;
  roundUp();
  res.right = _val-_inter.left;
  return res;
}//--------------------------------------------------------------------

//Operator *

Interval  operator *(const Interval& _inter1, const Interval& _inter2)
{

    if((iszero(_inter1.left)) && (iszero(_inter1.right))){
      return(Interval(0.0,0.0));
    }

    if(iszero(_inter2.left) && iszero(_inter2.right)){
      return(Interval(0.0,0.0));
    }
    
    Interval::BoundType ll,rr,t;

    if ((_inter1.left >= 0) && (_inter2.left >=0)){ // (++)(++)
      roundDown();
      ll=_inter1.left*_inter2.left;
      roundUp();
      rr=_inter1.right*_inter2.right;
    } else
    if ((_inter1.right<=0)   && (_inter2.right <= 0)) { // (--)(--)
      roundDown();
      ll=_inter1.right*_inter2.right;
      roundUp();
      rr=_inter1.left*_inter2.left;
    }else
    if ((_inter1.right <=0) && (_inter2.left <= 0)){ // (--)(-+)
                     // _inter2.right > 0 - from previous condition
      roundDown();
      ll=_inter1.left*_inter2.right;
      roundUp();
      rr=_inter1.left*_inter2.left;
    } else
    if ((_inter1.right <=0) && (_inter2.left >=0)){ // (--)(++)
      roundDown();
      ll=_inter1.left*_inter2.right;
      roundUp();
      rr=_inter1.right*_inter2.left;
    } else    // _inter1.right > 0 - from previous conditions
    if ((_inter1.left <=0) && (_inter2.right <= 0)) { // (-+)(--)
      roundDown();
      ll=_inter1.right*_inter2.left;
      roundUp();
      rr=_inter1.left*_inter2.left;
    } else
    if ((_inter1.left <=0) && (_inter2.left <=0) ){ // (-+)(-+)
      roundDown();
      ll=_inter1.left*_inter2.right;
      t=_inter2.left*_inter1.right;
      if (t<ll) ll=t;
      roundUp();
      rr=_inter1.left*_inter2.left;
      t=_inter1.right*_inter2.right;
      if (t>rr) rr=t;
    } else
    if (_inter1.left <=0) { // (-+)(++)
      roundDown();
      ll=_inter1.left*_inter2.right;
      roundUp();
      rr=_inter1.right*_inter2.right;
    } else // _inter1.left > 0
    if (_inter2.right <=0) { // (++)(--)
      roundDown();
      ll=_inter1.right*_inter2.left;
      roundUp();
      rr=_inter1.left*_inter2.right;
    } else // _inter2.right > 0
    /*if(_inter2.left <=0)*/{ // (++)(-+)
      roundDown();
      ll=_inter1.right*_inter2.left;
      roundUp();
      rr=_inter1.right*_inter2.right;
    }

    #ifdef DEBUGGING
    if(ll>rr)
    {
      throw intervalError("Error *** Fatal Interval error in operator*(Interval, Interval) .", _inter1.left, _inter1.right)
    }
    #endif
    return Interval(ll,rr);
}


Interval operator*(const Interval& _inter, const Interval::BoundType& _val)
{
   if((_inter.left==0) && (_inter.right==0))
   {
     return Interval(0,0);
   }
   if(_val==0.0)      
      return Interval(0,0);

   Interval res;
   if(_val>=0)
   {  
      roundDown();
      res.left = _inter.left*_val;
      roundUp();
      res.right = _inter.right*_val;
   }
   else
   {  
      roundDown();
      res.left = _inter.right*_val;
      roundUp();
      res.right = _inter.left*_val;
   }
   return res;
}


Interval operator*(const Interval::BoundType& _val,const Interval& _inter)
{
   if((_inter.left==0) && (_inter.right==0))
   {
     return Interval(0,0);
   }
   if(_val==0.0)      
      return Interval(0,0);

   Interval res;
   if(_val>=0)
   {  
      roundDown();
      res.left = _inter.left*_val;
      roundUp();
      res.right = _inter.right*_val;
   }
   else
   {  
      roundDown();
      res.left = _inter.right*_val;
      roundUp();
      res.right = _inter.left*_val;
   }
   return res;
}
Interval operator*(const Interval& _inter, double _val)
{

  if((_inter.left==0) && (_inter.right==0))
   {
     return Interval(0,0);
   }
   if(_val==0.0)      
      return Interval(0,0);

   Interval res;
   if(_val>=0)
   {  
      roundDown();
      res.left = _inter.left*_val;
      roundUp();
      res.right = _inter.right*_val;
   }
   else
   {  
      roundDown();
      res.left = _inter.right*_val;
      roundUp();
      res.right = _inter.left*_val;
   }
   return res;
}


Interval operator*(double _val, const Interval& _inter)
{
   if((_inter.left==0) && (_inter.right==0))
   {
     return Interval(0,0);
   }
   if(_val==0.0)      
      return Interval(0,0);

   Interval res;
   if(_val>=0)
   {  
      roundDown();
      res.left = _inter.left*_val;
      roundUp();
      res.right = _inter.right*_val;
   }
   else
   {  
      roundDown();
      res.left = _inter.right*_val;
      roundUp();
      res.right = _inter.left*_val;
   }
   return res;
}//--------------------------------------------------------------------

//Operator  /

Interval operator /(const Interval& _inter1, const Interval& _inter2)
{   Interval res;
    if(_inter2.left<=0 && _inter2.right>=0)
    {
      throw intervalError("Interval Error *** Possible division by zero.", _inter2.left,_inter2.right);
    }

    if(_inter1.right<=0 && _inter2.right<0) // (--)(--)
    {   roundDown();
        res.left=_inter1.right/_inter2.left;
        roundUp();
        res.right=_inter1.left/_inter2.right;
        #ifdef DEBUGGING
        if(res.left>res.right)
          throw intervalError(" Operator / (--)(--)",res.left,res.right);
        #endif
        return( res);
    }

    if( _inter1.right<=0 && _inter2.left>0) // (--)(++)
    {   roundDown();
        res.left=_inter1.left/_inter2.left;
        roundUp();
        res.right=_inter1.right/_inter2.right;
        #ifdef DEBUGGING
        if(res.left>res.right)
          throw intervalError(" Operator / (--)(++)",res.left,res.right);
        #endif
        return( res);
    }


    if(_inter1.left<=0 && _inter1.right>=0 && _inter2.right<0) // (-+)(--)
    {   roundDown();
        res.left=_inter1.right/_inter2.right;
        roundUp();
        res.right=_inter1.left/_inter2.right;
        #ifdef DEBUGGING
        if(res.left>res.right)
          throw intervalError(" Operator / (-+)(--)",res.left,res.right);
        #endif
        return( res);
    }


    if(_inter1.left<=0 && _inter1.right>=0 && _inter2.left>0) // (-+)(++)
    {   roundDown();
        res.left=_inter1.left/_inter2.left;
        roundUp();
        res.right=_inter1.right/_inter2.left;
        #ifdef DEBUGGING
        if(res.left>res.right)
          throw intervalError(" Operator / (-+)(++)",res.left,res.right);
        #endif
        return( res);
    }




    if(_inter1.left>=0 && _inter2.right<0)  // (++)(--)
    {   roundDown();
        res.left=_inter1.right/_inter2.right;
        roundUp();
        res.right=_inter1.left/_inter2.left;
        #ifdef DEBUGGING
        if(res.left>res.right)
          throw intervalError(" Operator / (++)(--)",res.left,res.right);
        #endif
        return( res);
    }


    if(_inter1.left>=0 && _inter2.left>0)  // (++)(++)
    {   roundDown();
        res.left=_inter1.left/_inter2.right;
        roundUp();
        res.right=_inter1.right/_inter2.left;
        #ifdef DEBUGGING
        if(res.left>res.right)
          throw intervalError(" Operator / (++)(++)",res.left,res.right);
        #endif
        return( res);
    }

    throw intervalError("Error *** Fatal Interval eres.rightor.",_inter2.left,_inter2.right);

  return(Interval(0,0));
}//--------------------------------------------------------------------

}}  // end of namespace capd::multiPrec

/// @}
