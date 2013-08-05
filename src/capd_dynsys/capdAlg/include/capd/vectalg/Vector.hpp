/////////////////////////////////////////////////////////////////////////////
/// @file Vector.hpp
///
/// @author Marian Mrozek, Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_VECTALG_VECTOR_HPP_ 
#define _CAPD_VECTALG_VECTOR_HPP_ 

#include <cmath>
#include <stack>
#include <stdexcept>
#include <cstdio>
#include <sstream>
#include <algorithm>
#include "capd/auxil/minmax.h"
#include "capd/basicalg/power.h"
#include "capd/vectalg/Container.hpp"
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/Vector_Interval.hpp"
#include "capd/vectalg/algebraicOperations.hpp"

namespace capd{
namespace vectalg{

//---------------------------constructors---------------------------//

template<typename Scalar,int dim>
Vector<Scalar,dim>::Vector(int A_dimension, const ScalarType data[]) : ContainerType(A_dimension,true)
{
  std::copy(data,data+A_dimension,begin());
}
template<typename Scalar,int dim>
Vector<Scalar,dim>::Vector(const char data[]) : ContainerType(dim,true)
{
   std::istringstream str(data);
   str >> *this;
}
template<typename Scalar,int dim>
Vector<Scalar,dim>::Vector(const std::string & data) : ContainerType(dim,true)
{
   std::istringstream str(data);
   str >> *this;
}
template<typename Scalar,int dim>
void Vector<Scalar,dim>::sorting_permutation(typename rebind<int>::other& perm)
{
  typedef typename rebind<int>::other IntVectorType;
  int i=0,j,k;

  if(dimension()!= perm.dimension())
     throw std::range_error("sorting_permutation: Incompatible vector dimensions");
  typename IntVectorType::iterator b=perm.begin(), e=perm.end();
  while(b!=e)
  {
    *b=i;
    ++i;
    ++b;
  }

  for(i=0;i<dimension();i++)
    for(j=dimension()-1;j>i;j--)
    {
      if((*this)[perm[j]] > (*this)[perm[j-1]])
      {
        k=perm[j-1];
        perm[j-1]=perm[j];
        perm[j]=k;
      }
    }
}


//----------------- input-output ----------------------------------//

template<typename Scalar, int dim>
std::ostream& operator<<(std::ostream& out, const Vector<Scalar,dim>& v)
{
   out << "{";
   if(v.dimension()>0){
     //if(v[0]>=Scalar(0)) out << " "; /***** DW it does not work for complex vectors ***/
     out << v[0];
   }
   for(int i=1;i<v.dimension();i++)
   {
      out << ",";
      // if(v[i]>=Scalar(0)) out << " "; /***** DW it does not work for complex vectors ***/
      out << v[i];
   }
   out << "}";
   return out;
}

template<typename Vector>
std::string vectorToString( const Vector & v, int firstIndex /*= 0*/, int lastIndex /*= -1*/,  int precision /* = -1*/){
  std::ostringstream out;
  if(precision>0)
       out.precision(precision);
  print(out, v, firstIndex, lastIndex);
  return out.str();
}

template<typename Vector>
std::ostream & printVector(std::ostream & out, const Vector & v, int firstIndex /*= 0*/, int lastIndex /*= -1*/){

  if((lastIndex < 0) || (lastIndex >= v.dimension()))
    lastIndex = v.dimension()-1;

  if(firstIndex < v.dimension()) {
    if(firstIndex < 0)
      firstIndex = 0;
    out << "{" << v[firstIndex];
    for(int i=firstIndex+1;i<=lastIndex;i++) {
      out << "," << v[i];
    }
    out << "}";
  } else {
    out << "{}";
  }
  return out;
}

template<typename Scalar, int dim>
std::istream& operator>> (std::istream& inp, Vector<Scalar,dim>& v)
{
   std::deque<Scalar> st;
   Scalar s;
   int ch;

   while('{'!=(ch=inp.get()) && ch!=EOF)
     ;
   if(ch!= EOF)
   {
/*
      // -- begin of added lines for empty vectors
      while(' '==(ch=inp.peek())) ch=inp.get();
      if('}'==(ch=inp.peek())){
        ch=inp.get();
        return inp;
      }
      // -- end of added lines for empty vectors
*/
      inp >> s;
      st.push_back(s);
      do{
         do{
            ch=inp.get();
         }while(isspace(ch));
         if(ch==','){
            inp >> s;
            st.push_back(s);
         }
      }while(ch!='}' && ch!=EOF);
   }
   if(inp.eof())
       throw std::ios_base::failure("EOF encountered when reading a vector");
   v.resize(st.size());
   std::copy(st.begin(), st.end(), v.begin());
   return inp;
}

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_VECTOR_HPP_ 
