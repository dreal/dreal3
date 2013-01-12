/// @addtogroup normalForms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file linearSubstitution.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_NORMALFORMS_LINEARSUBSTITUTION_HPP_ 
#define _CAPD_NORMALFORMS_LINEARSUBSTITUTION_HPP_ 
#include "capd/map/CnCoeff.h"

namespace capd{
namespace normalForms{

// -------------------------------------------------------------------------- //

// the following procedure brings linear part to the normal form
// IMPORTANT: s should contain a partial derivatives, not the power series coefficients!
// on output: partial derivatives of 
//       N \circ s \circ M
// where M,N are linear - usually N=M^{-1}, however we do not specify here how the inverse is computed

template<typename MatrixType>
capd::map::CnCoeff<MatrixType> linearSubstitution(
      const MatrixType& N,
      const capd::map::CnCoeff<MatrixType>& s,
      const MatrixType& M
   )
{
   typedef capd::vectalg::Multiindex::MultiindexVector MultiindexVector;
   typedef typename MatrixType::ScalarType ScalarType;
   int dimension = s.dimension();
   int rank = s.rank();

   capd::vectalg::Multiindex::IndicesSet indices;
   capd::vectalg::Multiindex::generateList(dimension,rank,indices);
   if(dimension!=M.numberOfRows() || dimension!=M.numberOfColumns() || dimension!=N.numberOfRows() || dimension!=N.numberOfColumns() )
   {
      throw std::runtime_error("normalForms::linearSubstitution - incompatible dimensions");
   }
   
   capd::map::CnCoeff<MatrixType> result (dimension,rank);

   for(int r=1;r<=rank;++r)
   {
      capd::vectalg::Multipointer mp = s.first(r);
      do{
         typename capd::map::CnCoeff<MatrixType>::VectorType temp(dimension);
         
         MultiindexVector::iterator b=indices[r-1].begin(), e=indices[r-1].end();
         while(b!=e)
         {
            ScalarType product = M((*b)[0]+1,mp[0]+1);
            for(int j=1;j<r;++j)
               product *= M((*b)[j]+1,mp[j]+1);

            capd::vectalg::Multipointer mp2(b->dimension(),b->begin());
            std::sort(mp2.begin(),mp2.end());
            temp += s(mp2)*product;
            ++b;
         }

         result(mp) = N*temp;
      }while(s.next(mp));
   }

   return result;
}


}} // namespace capd::normalForms

#endif // _CAPD_NORMALFORMS_LINEARSUBSTITUTION_HPP_ 

/// @}
