/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file SubVector.hpp
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2007 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_VECTALG_SUBVECTOR_HPP_
#define _CAPD_VECTALG_SUBVECTOR_HPP_

#include "capd/vectalg/SubVector.h"

namespace capd{
namespace vectalg{

template<typename VectorType1, typename VectorType2>
void intersectionWithSubvector(const VectorType1 & src, VectorType2 & target,
                               int start, int stop)
{
   bool result = true;
   for(int iTarget=start, iSrc=0; iTarget<stop; ++iTarget, ++iSrc)
      result = (result && intersection (src[iSrc], target[iTarget], target[iTarget]));
   if(!result)
     throw std::runtime_error(" Null intersection in intersectionWithSubvector ");
}


template<typename VectorType1, typename VectorType2>
void copyToSubvector(const VectorType1 & src, VectorType2 & target,
                     int start, int stop)
{
   for(int iTarget=start, iSrc=0; iTarget<stop; ++iTarget, ++iSrc)
      target[iTarget] = src[iSrc];

}

template<typename VectorType1, typename VectorType2>
void copyFromSubvector(const VectorType1 & src, VectorType2 & target,
                       int start, int stop)
{
   for(int iSrc=start, iTarget=0; iSrc<stop; ++iTarget, ++iSrc)
      target[iTarget] = src[iSrc];

}



template<typename MatrixType1, typename MatrixType2>
void intersectionWithSubmatrix( const MatrixType1 & src,
                                MatrixType2 & target,
                                int startRow, int stopRow,
                                int startCol, int stopCol)
{
   bool result =  true;
   for(int iTarget=startRow, iSrc=0; iTarget<stopRow; ++iTarget, ++iSrc)
      for(int jTarget=startCol, jSrc=0; jTarget<stopCol; ++jTarget, ++jSrc)
         result = (result && intersection(src[iSrc][jSrc], target[iTarget][jTarget], target[iTarget][jTarget]));
   if(!result)
     throw std::runtime_error(" Null intersection in intersectionWithSubvector ");
}


template<typename MatrixType1, typename MatrixType2>
void copyToSubmatrix(const MatrixType1 & src,
                     MatrixType2 & target,
                     int startRow, int stopRow,
                     int startCol, int stopCol)
{
   for(int iTarget=startRow, iSrc=0; iTarget<stopRow; ++iTarget, ++iSrc)
      for(int jTarget=startCol, jSrc=0; jTarget<stopCol; ++jTarget, ++jSrc)
         target[iTarget][jTarget] = src[iSrc][jSrc];
}


template<typename MatrixType1, typename MatrixType2>
void copyFromSubmatrix(const MatrixType1 & src,
                       MatrixType2 & target,
                       int startRow, int stopRow,
                       int startCol, int stopCol)
{
   for(int iSrc=startRow, iTarget=0; iSrc<stopRow; ++iTarget, ++iSrc)
      for(int jSrc=startCol, jTarget=0; jSrc<stopCol; ++jTarget, ++jSrc)
         target[iTarget][jTarget] = src[iSrc][jSrc];
}

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_SUBVECTOR_HPP_

/// @}
