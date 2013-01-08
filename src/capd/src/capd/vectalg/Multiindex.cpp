
/////////////////////////////////////////////////////////////////////////////
/// @file Multiindex.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/capd/factrial.h"
#include "capd/vectalg/Multiindex.h"
#include "capd/vectalg/Container.hpp"

namespace capd{
namespace vectalg{

// static members
std::vector<Multipointer::IndicesSet> Multipointer::indices;
int Multipointer::maxKnownLevel=0;

// static functions

// ---------------------------------------------------------------------

const Multipointer::IndicesSet& Multipointer::generateList(int p, int k)
{
   if(k<0 || k>p || p<1)
      throw std::runtime_error("subIndices: wrong arguments! Call with 1<= second <= first");
   
   if(p>maxKnownLevel)
   {
      indices.resize(((p+1)*p)/2);
      for(int i=maxKnownLevel+1;i<=p;++i)
         computeNextLevel();
   }
   return getList(p,k);
}

// ---------------------------------------------------------------------

void Multipointer::computeNextLevel()
{
   if(maxKnownLevel==0)
   {
      Multipointer first(1);
      MultipointersVector mv;
      mv.push_back(first);
      indices[0].push_back(mv);
      maxKnownLevel=1;
   }else
   {
      int p = maxKnownLevel+1;
      Multipointer first(p,true);
      
      int i=0;
      iterator b=first.begin(), e=first.end();
      while(b!=e)
      {
         *b = i;
         ++b;
         ++i;
      }
      //for k=0
      MultipointersVector mv;
      mv.push_back(first);
      getList(p,1).push_back(mv);

      for(int k=2;k<=maxKnownLevel;++k)
      {
         Multipointer last(1,&maxKnownLevel);
         IndicesSet& current = getList(p,k);

         const IndicesSet& lower = getList(maxKnownLevel,k-1);
         IndicesSet::const_iterator b = lower.begin(), e=lower.end();
         while(b!=e)
         {
            MultipointersVector mv = *b;
            mv.push_back(last);
            current.push_back(mv);
            ++b;
         }
         
         const IndicesSet& higher = getList(maxKnownLevel,k);
         b = higher.begin();
         e = higher.end();
         while(b!=e)
         {
            for(unsigned int s=0;s<(*b).size();++s)
            {
               MultipointersVector copy = *b;
               copy[s] = sumMultipointers((*b)[s],last);
               current.push_back(copy);
            }
            ++b;
         }
      }

      // for k=maxKnownLevel+1
      MultipointersVector last;
      for(int s=0;s<p;++s)
      {
         Multipointer mv(1,&s);
         last.push_back(mv);
      }
      getList(p,p).push_back(last);

      ++maxKnownLevel;
   }
}

// ---------------------------------------------------------------------

void Multiindex::generateList(int n, int k, IndicesSet& result)
{
   result.resize(k);
   //we storage the first level, i.e. k=1
   int i;
   for(i=0;i<n;++i)
      result[0].push_back(Multiindex(1,&i));
   
   for(i=1;i<k;++i)
   {
      MultiindexVector::iterator b = result[i-1].begin(), e=result[i-1].end();
      while(b!=e)
      {
         for(int j=0;j<n;++j)
         {
            Multiindex m(i+1);
            for(int c=0;c<i;++c)
               m[c] = (*b)[c];
            m[i] = j;
            result[i].push_back(m);
         }
         ++b;
      }
   }
}

// ---------------------------------------------------------------------

long Multipointer::factorial() const{
   const_iterator b=begin(), e=end();
   long result=1;
   while(b!=e)
   {
      const_iterator temp=b;
      int p = *b;
      do{
         ++b;
      }while(b!=e && *b==p);
      size_t n = b-temp;
      if(n>1)
         result *= ::factorial(n);
   }
   return result;
}

// ---------------------------------------------------------------------
/// Returns multipointer containing entries which indices are in mp
///
/// e.g. for a = (1,3,3,6,7)  mp=(1,2,4)
///   a.subMultipointer(mp)  returns (3,3,7)
///
Multipointer Multipointer::subMultipointer(const Multipointer& mp) const
{
   Multipointer result(mp.dimension(),true);
   iterator i=result.begin();
   const_iterator j=begin();
   const_iterator b=mp.begin(), e=mp.end();
   while(b!=e)
   {
      (*i) = *(j+(*b));
      ++i;
      ++b;
   }
   return result;
}

// ---------------------------------------------------------------------
/// returns sum of the multiindex entries
int Multiindex::module() const{
   const_iterator b=begin(), e=end();
   int result=0;
   while(b!=e)
   {
      result += (*b); // assume Multiindex has nonnegative coordinates only
      ++b;
   }
   return result;
}

// ---------------------------------------------------------------------
/// for multiindex (a,b,..,n) returns a!b!...n!
long Multiindex::factorial() const{
   const_iterator b=begin(), e=end();
   long result=1;
   while(b!=e)
   {
      if((*b)>1)
         result *= ::factorial(*b);
      ++b;
   }
   return result;
}

// ---------------------------------------------------------------------

Multiindex::Multiindex(int A_dimension, const Multipointer& mp) : Vector<int,0>(A_dimension)
{
   Multipointer::const_iterator b=mp.begin(), e=mp.end();
   while(b!=e)
   {
      ++ ((*this))[*b];
      ++b;
   }
}


// ---------------------------------------------------------------------

Multipointer::Multipointer(const Multiindex& mi) : Vector<int,0>(mi.module(),true)
{
   iterator i=begin();
   for(int j=0;j<mi.dimension();++j)
   {
      for(int r=0;r<mi[j]; ++r)
      {
         (*i) = j;
         ++i;
      }
   }
}

// ---------------------------------------------------------------------

// this function just concatenate sorted Multipointers to the another sorted Multipointer
Multipointer sumMultipointers(const Multipointer& x, const Multipointer& y)
{
   Multipointer result(x.module()+y.module());
   Multipointer::const_iterator xb=x.begin(), xe=x.end(), yb=y.begin(), ye=y.end();
   Multipointer::iterator b=result.begin();
   while(xb!=xe && yb!=ye)
   {
      if((*xb)<(*yb))
      {
         (*b) = (*xb);
         ++xb;
      }else{
         (*b) = (*yb);
         ++yb;
      }
      ++b;
   }
   if(xb==xe)
   {
      xb = yb;
      xe = ye;
   }
   while(xb!=xe)
   {
      (*b) = (*xb);
      ++b;
      ++xb;
   }
   return result;
}

Multipointer addIndex(const Multipointer & mp, int index) {
  Multipointer result(mp.dimension() + 1);
  Multipointer::iterator res = result.begin();
  Multipointer::const_iterator src = mp.begin(), end = mp.end();
  while(src != end){
    if((index>=0) && (index < *src)) {
      *res = index;
      index = -1;
      res++;
    }
    *res = *src;
    ++res; ++src;
  }
  if(res != result.end()){
    *res = index;
  }
  return result;
}

Multipointer push_back(const Multipointer & mp, int index) {
  Multipointer result(mp.dimension() + 1);
  Multipointer::iterator res = result.begin();
  Multipointer::const_iterator src = mp.begin(), end = mp.end();
  while(src != end){
    *res = *src;
    ++res; ++src;
  }
  *res = index;
  return result;
}

}} // namespace capd::vectalg

