//////////////////////////////////////////////////////////////////////////////
///
///  @file TexWriter.h
///  
///  @author kapela  @date   Apr 17, 2011
//////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2011 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_BASICALG_TEXWRITER_H_
#define _CAPD_BASICALG_TEXWRITER_H_

#include "capd/intervals/Interval.h"
#include "capd/rounding/RoundingTraits.h"
#include "capd/vectalg/Vector.h"
#include <complex>
#include <deque>
#include <iostream>
#include <cassert>
#ifdef __USE_FILIB__
#include "capd/filib/Interval.h"
#endif

namespace capd {

using capd::rounding::setRounding;

template<typename T>
std::string printToString(const T & data, int precision){
  std::ostringstream buf;
  buf.precision(precision);
  buf << std::fixed << data;
  return buf.str();
}

//-------------------------------------------------------------------------------

class TexWriter { //: public std::ostream

protected:
  std::ostream & out;
public:
  enum FloatStyle { FloatSci, FloatFix, FloatFix2 };
  FloatStyle floatStyle;
  std::string baseSymbol;
  std::string iSymbol;
  std::string vectorStartSymbol;
  std::string vectorEndSymbol;
  std::string vectorSeparator;
  std::string equationBeginSymbol;
  std::string equationEndSymbol;
  std::string plusSymbol;


  TexWriter(std::ostream & output)
  : out(output),
    floatStyle(FloatFix) {
    setBaseStyle(0);
    setISymbol(0);
    setVectorStyle(0);
    setEquationSymbol(0);
    setPlusSymbol(0);
  }
  template <typename T>
  T putDigits(std::deque<int> & container, int & sign, T number, int n, int precision);
  void writeSciInterval(const std::deque<int> & dl, const std::deque<int> & dr,
                        int p, int l_sign, int len );
  void writeFixInterval(const std::deque<int> & dl, const std::deque<int> & dr,
                        int p, int l_sign, int intDigits, int prec);
  template<typename IntervalType>
  void writeInterval(const IntervalType& intv);
  template <typename VectorType>
  void writeVector(const VectorType & x);

  int precision(){
    return out.precision();
  }
  TexWriter &  precision(int newPrecision){
    out.precision(newPrecision);
    return *this;
  }
  TexWriter & setFloatStyle(FloatStyle style){
    floatStyle = style;
    return *this;
  }
  /// Sets style of a base.
  /// i=0 C convention for exponents e.g 1.0e-5
  /// i=1 TeX e.g. 1.0\cdot 10^{-5}
  TexWriter &  setBaseStyle(int i){
    baseSymbol = (i==0)? "\\mbox{e}" :
                 (i==1)? "\\cdot 10^" :
                   "";
    return *this;
  }
  /// sets imaginary symbol i.
  TexWriter &  setISymbol(int i){
      iSymbol = (i==1)? "\\ii " : "\\mbox{i\\,}";
      return *this;
  }
  /// sets vector style
  TexWriter &  setVectorStyle(const std::string & start, const std::string & end, const std::string & separator){
    vectorStartSymbol = start;
    vectorEndSymbol = end;
    vectorSeparator = separator;
    return *this;
  }
  /**
   *  sets vector style.
   *  * i=0  sequence : (1, 3, 4)
   *  * i=1  CAPD vectors : {1, 3, 4}
   *  * i=2  vertical vector
   */
  TexWriter &  setVectorStyle(int i){
    switch(i){
      case 0:
        setVectorStyle("(", ")", ",\\;");
        break;
      case 1:
        setVectorStyle("\\{", "\\}", ",\\;");
        break;
      case 2: // vertical vector
        setVectorStyle("\\left(\\begin{array}{c}\n", "\n\\end{array}\\right)", "\\\\\n");
        break;
    }
    return *this;
  }
  std::string getEquationBeginSymbol(int i){
    return (i==0)? "":
           (i==1)? "$":
           (i==2)? "\\[" : "";
  }
  std::string getEquationEndSymbol(int i){
    return (i==0)? "":
           (i==1)? "$":
           (i==2)? "\\]" : "";
  }
  TexWriter &  setEquationSymbol(int i){
    equationBeginSymbol = getEquationBeginSymbol(i);
    equationEndSymbol = getEquationEndSymbol(i);
    return *this;
  }
  TexWriter &  setPlusSymbol(int i){
    plusSymbol = (i==0) ? "+" :
                 (i==1) ? "\\;\\;\\;" :
                          "";
    return *this;
  }

  template <typename T>
  TexWriter & write(const T & x, int equationStyle = -1);

  void writeDocumentHeader(std::string parameters = ""){
    out << "\\documentclass[a4paper,10pt]{article} \n"
        << "\\usepackage[utf8x]{inputenc} \n"
        << parameters
        << "\\begin{document} \n";
  }
  void writeDocumentFooter(){
    out <<  "\n\\end{document} \n";
  }

  template<typename T>
  friend TexWriter & operator<<(TexWriter & o, const T & x);
  friend TexWriter & operator<<(TexWriter & o, std::ostream& (*fn)(std::ostream&));

};

template<typename T>
TexWriter & operator<< (TexWriter & o, const T & x){
  o.out << x;
  return o;
}

template<typename T, typename R>
TexWriter & operator<< (TexWriter & o, const capd::intervals::Interval<T, R> & x){
  o.writeInterval(x);
  return o;
}
#ifdef __USE_FILIB__
template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
TexWriter & operator<< (TexWriter & o, const capd::filib::Interval<T, R, M> & x){
  o.writeInterval(x);
  return o;
}
#endif
template<typename T>
TexWriter & operator<< (TexWriter & o, const std::complex<T> & x){
  o << x.real();
  if (x.imag() < 0 )
    o<< " - " << o.iSymbol << -x.imag();
  else
    o <<" + " << o.iSymbol << x.imag();
  return o;
}

template<typename T, int dim>
TexWriter & operator<< (
    TexWriter & o,
    const capd::vectalg::Vector<T, dim> & x){
  o.writeVector(x);
  return o;
}

inline TexWriter & operator<<(TexWriter & o, std::ostream& (*fn)(std::ostream&)) {
    fn(o.out);
    return o;
}

inline int numberOfDigits(int n){
  return n!=0 ? floor( log10( abs( n ) ) ) + 1 : 0;
}

//inline std::ostream & operator << (std::ostream & o , const std::deque<int> & c){
//  for(unsigned int i=0; i < c.size(); i++)
//    o << c[i];
//  return o;
//}

///////////////////////////////////////////////////////////////////////////////
//  putDigits
///
/// It parses \b number and puts its \b nDigits digits in \b container.
///
/// @return part of number that remained after parsing
///////////////////////////////////////////////////////////////////////////////
template <typename T>
T TexWriter::putDigits(
    std::deque<int> & container,   ///< [out] container where digits will be stored
    int & sign,                    ///< [out] returns sign of number
    T number,                      ///< [in]  number to be parsed
    int nDecDigits,                ///< [in]  number of decimal digits of a given number to be stored in container
    int nDigits                    ///< [in]  total number of digits to be stored in container
){

  sign = (number==0)? 0 : (number < 0)? -1 : 1;

  if(sign == -1)
    number = -number;

  int intPart = toInt(number);
  //std::cout <<"\n number : "<< number <<  "\n  intPart " << intPart;

  number -= intPart;
  //std::cout <<"\n number : "<< number ;

  int i=0;
  for(; i<nDecDigits; ++i){
    container.push_front(intPart % 10);
    intPart /= 10;
    //std::cout <<"\n i : "<< i <<  "  intPart " << intPart << " digit " << container[0];
  }

  for(; i<nDigits; ++i){
    number *= 10;
    int digit = toInt(number);
    container.push_back(digit);
    number -= digit;
    //std::cout << "\n i : "<< i <<  "  number " << number << " digit " << container[i];
  }
  container.resize(nDigits);
  return (nDecDigits<=nDigits)? number : T(1.0);
}

/// Rounds up parsed number stored in d
void roundUp(
    std::deque<int> & d    ///< container with consecutive digits of a number
 ){
  int carry = 1;
  for(int i=d.size()-1; i>=0 && carry; --i){
    ++d[i];
    if(d[i]>=10){
      d[i]=0;
    } else {
      carry = 0;
    }
  }
}

void TexWriter::writeSciInterval(
    const std::deque<int> & dl,
    const std::deque<int> & dr,
    int p,
    int l_sign,
    int len
){

int z=0;
 if(l_sign < 0){   // r_sign is always positive
   out << "{}_{-";
 } else {
   while(z<len && dl[z]==dr[z]){
     out << dl[z];
     if(z==0)
       out << ".";
     ++z;
   }
   if(!z)
     out << "{}";
   out << "_{";
 }

 for(int s=z; s<len; ++s){
   out << dl[s];
   if(s==0)
     out << ".";
 }
 out << "}";

 out << "^{";
 if(!z && l_sign<0)
   out << plusSymbol;
   //out << "\\;\\;\\;";
 for(int s=z; s<len; ++s){
   out << dr[s];
   if(s==0)
     out << ".";
 }
 out << "}";

 if(p!=0){
     out << this->baseSymbol << "{" << p << "}";
 }
}

void TexWriter::writeFixInterval(
    const std::deque<int> & dl,
    const std::deque<int> & dr,
    int p,
    int l_sign,
    int intDigits,
    int len
){

  int z=0;
  bool l_started = false,  r_started=false;


  if(l_sign < 0){   // r_sign is always positive
    out << "{}_{";
    if(intDigits==0){
      out <<"-0.";
      l_started = true;
    }
  } else {
    if(intDigits==0){
      out <<"0.";
      l_started = true; r_started = true;
    }
    while(z<len && dl[z]==dr[z]){
      out << dl[z];
      l_started = true; r_started = true;
      ++z;
      if(z==intDigits)
        out << ".";
    }
    if(!z)
      out << "{}";
    out << "_{";
  }
  for(int s=z; s<len; ++s){
    if(l_started) {
           out << dl[s];
      }else{
        if( dl[s]!=0){
           l_started = true;
           if(l_sign < 0)
             out << "-";
           out << dl[s];
         } else {
           if(s!=intDigits-1)
             out << "\\;\\;";
         }
      }

    if(s==intDigits-1){
      out << ((l_started)? "." : (l_sign < 0)? "-0.":"0.");
      l_started = true;
    }
  }
 out << "}";

 out << "^{";
 if(l_sign<0){
   out << plusSymbol;
   if(intDigits==0){
     out <<"0.";
     r_started = true;
   }
 }
   //out << "\\;\\;\\;";

 for(int s=z; s<len; ++s){

   if(r_started) {
        out << dr[s];
   }else{
     if( dr[s]!=0){
        r_started = true;
        out << dr[s];
      } else {
        if(s!=intDigits-1)
          out << "\\;\\;";
      }
   }
      if(s==intDigits-1){
        out << ((r_started)? "." : "0.");
        r_started = true;
      }
 }
 out << "}";

// if(p!=0){
//     out << this->baseSymbol << "{" << p << "}";
// }
}
template<typename IntervalType>
void TexWriter::writeInterval(const IntervalType& intv){

  typedef typename IntervalType::BoundType Float;
  Float l = intv.leftBound();
  Float r = intv.rightBound();
  if(l==0 && r==0){
    out << printToString(l, out.precision());
    return;
  }
  if(r<=0){
    Float t = r;  r = -l;   l = -t;
    out << "-";
  }
  int nl = numberOfDigits(toInt(l));
  int nr = numberOfDigits(toInt(r));
  int n = std::max(nl, nr);
  int prec = out.precision();
  int p = 0;
  int len = 0;

  switch(floatStyle){
    case FloatSci:
      len = prec + 1;
      if(n>0){
        p = n - 1;
      } else {
        // we determine negative exponent
        while(capd::abs(l)<1 && capd::abs(r)<1) {
          --p;
          setRounding<Float>(capd::rounding::RoundDown);
          l*=10;
          setRounding<Float>(capd::rounding::RoundUp);
          r*=10;
        }
        n=1;
      }
      break;
    case FloatFix:
      len = n + prec;
      break;
    case FloatFix2:
      len = std::max(n, prec);
      break;
  }


  std::deque<int> dl, dr;
  int l_sign, r_sign;
  setRounding<Float>(capd::rounding::RoundDown);
  Float l_rem = putDigits(dl, l_sign, l, n, len);
  setRounding<Float>(capd::rounding::RoundUp);
  Float r_rem = putDigits(dr, r_sign, r, n, len);

  assert(r_sign > 0);

  if(l_sign < 0 && l_rem != 0)
    roundUp(dl);
  if(r_sign > 0 && r_rem != 0)
    roundUp(dr);

  if(floatStyle == FloatSci)
    writeSciInterval(dl, dr, p, l_sign, len );
  else
    writeFixInterval(dl, dr, p, l_sign, n, len );
}

//template<typename IntervalType>
//void TexWriter::writeInterval(const IntervalType& intv){
//
//
//  typedef typename IntervalType::BoundType Float;
//  Float l = intv.leftBound();
//  Float r = intv.rightBound();
//  if(l==0 && r==0){
//    out << printToString(l, out.precision(), capd::rounding::RoundCut);
//    return;
//  }
//  if(r<=0){
//    Float t = r;  r = -l;   l = -t;
//    out << "-";
//  }
//  int nl = numberOfDigits(int(l));
//  int nr = numberOfDigits(int(r));
//
//  std::deque<int> dl, dr;
//
//  // we determine exponent
//  int p=0;
//  while((capd::abs(l)>10) || (capd::abs(r)>10)) {
//    ++p;
//    setRounding<Float>(capd::rounding::RoundDown);
//    l/=10;
//    setRounding<Float>(capd::rounding::RoundUp);
//    r/=10;
//  }
//
//  while(capd::abs(l)<1 && capd::abs(r)<1) {
//    --p;
//    setRounding<Float>(capd::rounding::RoundDown);
//    l*=10;
//    setRounding<Float>(capd::rounding::RoundUp);
//    r*=10;
//  }
//
//  int prec = out.precision();
//  std::string t1 = printToString(l, prec, capd::rounding::RoundDown),
//              t2 = printToString(r, prec, capd::rounding::RoundUp);
//  int len1 = t1.size(),
//      len2 = t2.size(),
//      len = std::min(len1,len2);
//  int z=0, s;
//  while(z<len && t1[z]==t2[z]){
//    out << t1[z];
//    ++z;
//  }
//  if(!z)
//    out << "{}";
//
//  out << "_{";
//  for(s=z; s<len1; ++s)
//    out << t1[s];
//  for(;s<=prec;++s)
//    out << "0";
//  out << "}";
//
//  out << "^{";
//  if(!z && l<0)
//    out << "\\;\\;\\;";
//  for(s=z;s<len2;++s)
//    out << t2[s];
//  for(;s<=prec;++s)
//    out << "0";
//  out << "}";
//
//  if(p!=0){
//      out << this->base << "{" << p << "}";
//  }
//}

template <typename VectorType>
void TexWriter::writeVector(const VectorType & v){

  out << vectorStartSymbol;
  if(v.dimension()>0){
    (*this) << v[0];
  }
  for(int i=1; i<v.dimension(); i++) {
    out << vectorSeparator;
    (*this) << v[i];
  }
  out << vectorEndSymbol;
}

template <typename T>
TexWriter & TexWriter::write(const T & x, int eqStyle ){
  out << ((eqStyle<0) ? equationBeginSymbol : getEquationBeginSymbol(eqStyle) );
  (*this)<< x;
  out << ((eqStyle<0) ? equationEndSymbol : getEquationEndSymbol(eqStyle) );
  return (*this);
}


} // end of namespace capd

#endif /* _CAPD_BASICALG_TEXWRITTER_H_ */
