/////////////////////////////////////////////////////////////////////////////
/// @addtogroup Interval
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file mpInterval.hpp
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifdef __HAVE_MPFR__

namespace capd{
namespace multiPrec{
   
   
   
//------------'inline' function for the class 'Interval'
class intervalError : public std::runtime_error{

public:         
  intervalError( const char * msg, 
               const Interval::BoundType& _left, 
               const Interval::BoundType& _right) 
    : runtime_error(msg), left(_left), right(_right)
  {}

  virtual ~intervalError() throw()
  {}

  const char * what() const throw()
  {
    std::ostringstream str;
    str << "Interval error: " << runtime_error::what() << "left=" << left << " right=" << right;
    return str.str().c_str();
  }

protected: 
  Interval::BoundType left, right;

};

//------------ constructors -------------------------------

inline  Interval::Interval(const BoundType &_value) : 
        left(_value), right(_value) 
{}


inline Interval::Interval(const BoundType &_left, const BoundType &_right):
       left(_left),right(_right)
{
   if (left > right)
      throw intervalError("Interval constructor error!",left,right);
}


inline  Interval::Interval(double _value) : 
        left(_value), right(_value) 
{}


inline Interval::Interval(double _left, double _right):
       left(_left),right(_right)
{
   if (left > right)
      throw intervalError("Interval constructor error!",left,right);
}


// a copying constructor

inline Interval::Interval(const Interval& iv)
{
   left = iv.left;
   right = iv.right;
}

//-----------------------------------------------------------------------------------

// --- INCLUSIONS ------------------

//Number inclusion _value \in iv
inline bool in(const Interval::BoundType & _value,const Interval& iv){
   return ( _value >= iv.leftBound() && _value <= iv.rightBound() );
}

//Interval inclusion
//  returns 1 if small_iv \subset \interior in, if interior==1
//          1 if small_iv \subset \interior in, if interior==0
//   0 - otherwise

inline bool in(const Interval& small_iv ,const Interval& iv,int interior)
{
   if (!interior)
     return ( small_iv.left >= iv.left && small_iv.right <= iv.right );
   else
     return ( small_iv.left > iv.left && small_iv.right < iv.right );
}




//maximum
inline Interval  max(const Interval & iv1, const Interval & iv2)
{
   return Interval ((iv1.leftBound()>iv2.leftBound() ? iv1.leftBound() : iv2.leftBound()),
                                (iv1.rightBound()>iv2.rightBound() ? iv1.rightBound() : iv2.rightBound()));
}

//minimum
inline Interval  min(const Interval & iv1, const Interval & iv2)
{
   return Interval ((iv1.leftBound()<iv2.leftBound() ? iv1.leftBound() : iv2.leftBound()),
                                (iv1.rightBound()<iv2.rightBound() ? iv1.rightBound() : iv2.rightBound()));
}

}// end of namespace multiprec

inline multiPrec::Interval  max(const multiPrec::Interval & iv1, const multiPrec::Interval & iv2)
{
   return multiPrec::max(iv1, iv2);
}
inline multiPrec::Interval  min(const multiPrec::Interval & iv1, const multiPrec::Interval & iv2)
{
   return multiPrec::min(iv1, iv2);
}  

namespace multiPrec{

// Diameter

inline Interval  diam(const Interval & iv)
{
   return(right(iv)-left(iv));
}

//midpoint

inline Interval  mid(const Interval & iv)
{
   return((right(iv)+left(iv))/Interval(2.0));
}

inline Interval  Interval::mid() const
{  
   roundUp();	
   return Interval(right+left)/Interval(2.0);
}

//nonnegative part

inline Interval  nonnegativePart(const Interval & iv)
{
   if(iv.rightBound()>=0)
      return Interval (max(Interval::BoundType(0.),iv.leftBound()), iv.rightBound() );
   else
   {
      throw intervalError("Nonnegative part is empty.", iv.leftBound(), iv.rightBound());
   }
}



inline Interval ball(const Interval& iv,const Interval &r)
{
   return Interval ( (iv-r).leftBound(),(iv+r).rightBound() );
}




inline Interval left(const Interval &iv){
  return Interval(iv.left);
}


inline Interval right(const Interval &iv){
  return Interval(iv.right);
}


inline bool Interval::contains(const Interval::BoundType& x) const
{
   return (left <= x) && (x<=right);
}

inline bool Interval::subset(const Interval &iv) const
{
   return (left >= iv.left) && (right<=iv.right);
}

inline bool Interval::subsetInterior(const Interval &iv) const
{
   return (left > iv.left) && (right<iv.right);
}



//----        RELATIONS -----------------------------------------------------------


//the relation  ==

inline bool operator ==(const Interval& iv1, const Interval& iv2)
{
   return( (iv1.left==iv2.left) && (iv1.right==iv2.right));
}

// weak inequality relation <=

inline bool operator <=(const Interval& iv1, const Interval& iv2)
{
   return(iv1.right<=iv2.left);
}

// strong inequality <

inline bool operator <(const Interval& iv1, const Interval& iv2)
{
   return(iv1.right<iv2.left);
}

//weak inequality relation >=

inline bool operator >=(const Interval& iv1, const Interval& iv2)
{
   return(iv1.left>=iv2.right );
}

//strong inequality relation >

inline bool operator >(const Interval& iv1, const Interval& iv2)
{
   return(iv1.left>iv2.right);
}

//the relation  !=  ( as a negation of  ==)

inline bool operator !=(const Interval& iv1, const Interval& iv2)
{
   return(iv1.left!=iv2.left || iv1.right!=iv2.right);
}


// sending an Interval to a stream

inline std::ostream& operator <<(std::ostream& s, const Interval& iv)
{
   roundNearest();
   return(s << "[" << iv.left << "," << iv.right << "]");
}

// -------  operator unary -    --------------------------------------------------

inline Interval operator-(const Interval& iv)
{
   return(Interval(-iv.right,-iv.left));
}


//a different operator for powers

inline Interval operator^(const Interval& value, int ile)
{
   return power(value, ile);
}

}}  // end of namespace capd::multiPrec

#endif  // __HAVE_MPFR__

/// @}
