#if !defined(_RATIONALNUMBER_H_)
#define _RATIONALNUMBER_H_
/*
  //########################### rationalNumber class ################################//
  Autor: Marian Mrozek, Kraków 2003.
*/

#include <iostream>
#include <stdexcept>

//######################## declarations ###########################//

template <class intType>
class rationalNumber;

template <class intType>
rationalNumber<intType> operator-(const rationalNumber<intType> &v);        // negations
template <class intType>
rationalNumber<intType> operator+(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);   // sum
template <class intType>
rationalNumber<intType> operator-(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);   // substraction
template <class intType>
rationalNumber<intType> operator*(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);   // multiplication
template <class intType>
rationalNumber<intType> operator/(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);   // division
template <class intType>
int operator< (const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);
template <class intType>
int operator> (const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);
template <class intType>
int operator<=(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);
template <class intType>
int operator>=(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);
template <class intType>
int operator==(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);
template <class intType>
int operator!=(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);
template <class intType>
std::ostream &operator<<(std::ostream &out,const rationalNumber<intType> &v);
template <class intType>
std::istream &operator>>(std::istream &inp, rationalNumber<intType> &v);
template <class intType>
bool isDivisible(const rationalNumber<intType> &v1,const rationalNumber<intType> &v2);
template <class intType>
bool isZero(const rationalNumber<intType> &v);

//########################### Class rationalNumber ################################//

template <class intType>
class rationalNumber{

  public:


  void normalize();

  // constructors
  rationalNumber(){p=0;q=1;normalize();};
  rationalNumber(int k){p=k;q=1;normalize();};
  rationalNumber(intType k,intType l){p=k;q=l;normalize();};

  // unary operation
  friend rationalNumber operator- <>(const rationalNumber &v);        // negation

  // binary operations
  friend rationalNumber operator+ <>(const rationalNumber &v1,const rationalNumber &v2);   // sum
  friend rationalNumber operator- <>(const rationalNumber &v1,const rationalNumber &v2);   // substraction
  friend rationalNumber operator* <>(const rationalNumber &v1,const rationalNumber &v2);   // multiplication
  friend rationalNumber operator/ <>(const rationalNumber &v1,const rationalNumber &v2);   // division


  // assigment operators
  rationalNumber &operator= (const rationalNumber &s); 
  rationalNumber &operator+=(const rationalNumber &s);  
  rationalNumber &operator-=(const rationalNumber &s);
  rationalNumber &operator*=(const rationalNumber &s);
  rationalNumber &operator/=(const rationalNumber &s);

  // relation operatos
  friend int operator<  <>(const rationalNumber &v1,const rationalNumber &v2);
  friend int operator>  <>(const rationalNumber &v1,const rationalNumber &v2);
  friend int operator<= <>(const rationalNumber &v1,const rationalNumber &v2);
  friend int operator>= <>(const rationalNumber &v1,const rationalNumber &v2);
  friend int operator== <>(const rationalNumber &v1,const rationalNumber &v2);
  friend int operator!= <>(const rationalNumber &v1,const rationalNumber &v2);

  // input/ output
  friend std::ostream &operator<< <>(std::ostream &out,const rationalNumber &v);
  friend std::istream &operator>> <>(std::istream &inp, rationalNumber &v);

	friend bool isZero <>(const rationalNumber &v);
	
	// conversion operators
	operator double();

  private:

  intType p,q; //numerator, denominator

};// end of rationalNumber class

template <class intType>
rationalNumber<intType> operator-(const rationalNumber<intType> &r){
  rationalNumber<intType> s;
  s.p=-r.p;
  s.q=r.q;
  return s;
}

template <class intType>
rationalNumber<intType> operator+(const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  rationalNumber<intType> s;
  s.p=r1.p*r2.q+r1.q*r2.p;
  s.q=r1.q*r2.q;
  s.normalize();
  return s;
}

template <class intType>
rationalNumber<intType> operator-(const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  rationalNumber<intType> s;
  s.p=r1.p*r2.q-r1.q*r2.p;
  s.q=r1.q*r2.q;
  s.normalize();
  return s;
}

template <class intType>
rationalNumber<intType> operator*(const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  rationalNumber<intType> s;
  s.p=r1.p*r2.p;
  s.q=r1.q*r2.q;
  s.normalize();
  return s;
}

template <class intType>
rationalNumber<intType> operator/(const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
	if(r2.p == intType(0)) 
		throw "rationalNumber::operator/::Could not divide by zero";
  rationalNumber<intType> s;
  s.p=r1.p*r2.q;
  s.q=r1.q*r2.p;
  s.normalize();
  return s;
}


//assignment operators
template <class intType>
rationalNumber<intType> &rationalNumber<intType>::operator=(const rationalNumber<intType> &r){
 p=r.p;
 q=r.q;
 return *this;
}

template <class intType>
rationalNumber<intType> &rationalNumber<intType>::operator+=(const rationalNumber<intType> &r){
 p=p*r.q+q*r.p;
 q*=r.q;
 normalize();
 return *this;
}

template <class intType>
rationalNumber<intType> &rationalNumber<intType>::operator-=(const rationalNumber<intType> &r){
 p=p*r.q-q*r.p;
 q*=r.q;
 normalize();
 return *this;
}

template <class intType>
rationalNumber<intType> &rationalNumber<intType>::operator*=(const rationalNumber<intType> &r){
 p*=r.p;
 q*=r.q;
 normalize();
 return *this;
}

template <class intType>
rationalNumber<intType> &rationalNumber<intType>::operator/=(const rationalNumber<intType> &r){
 p*=r.q;
 q*=r.p;
 normalize();
 return *this;
}

// relational operators

template <class intType>
int operator< (const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  return r1.p*r2.q<r1.q*r2.p;
}

template <class intType>
int operator> (const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  return r1.p*r2.q>r1.q*r2.p;
}

template <class intType>
int operator<=(const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  return r1.p*r2.q<=r1.q*r2.p;
}

template <class intType>
int operator>=(const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  return r1.p*r2.q>=r1.q*r2.p;
}

template <class intType>
int operator==(const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  return r1.p*r2.q==r1.q*r2.p;
}

template <class intType>
int operator!=(const rationalNumber<intType> &r1,const rationalNumber<intType> &r2){
  return r1.p*r2.q!=r1.q*r2.p;
}

// input - ouput

template <class intType>
std::ostream &operator<<(std::ostream &out,const rationalNumber<intType> &r){
  out << r.p;
  if(r.q > 1) out << "/" << r.q;
  return out;
}

template <class intType>
std::istream &operator>>(std::istream &inp, rationalNumber<intType> &r){
  while(' '==inp.peek())inp.get();
  inp >> r.p;
  if(inp.peek()!='/') r.q=1;
  else{
    inp.get();
    inp >> r.q;
  }
  return inp;
}


// conversion operator
template <class intType>
rationalNumber<intType>::operator double(){
	return double(p)/double(q);
}

template <class intType>
bool isDivisible(const rationalNumber<intType> &a,const rationalNumber<intType> &b)
{
	return true;
}

template <class intType>
bool isZero(const rationalNumber<intType> &v)
{
	return v.p == 0;
}

template <class intType>
void rationalNumber<intType>::normalize(){
  intType m,n,r;
  if(!q){
    throw std::out_of_range("rationalNumber<intType>::normalize: Denominator cannot be zero");
  }
  if(p){
    m=p;n=q;
    if(m>n){
      r=n;n=m;m=r;
    }
    while((r=(n%m))!=0){
      n=m; m=r;
    }
    p/=m;
    q/=m;
  }else q=1;
  if(q<0){
    p=-p;q=-q;
  }
}

#endif //_RATIONALNUMBER_H_



