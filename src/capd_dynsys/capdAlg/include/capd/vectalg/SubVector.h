/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file SubVector.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2007 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_VECTALG_SUBVECTOR_H_
#define _CAPD_VECTALG_SUBVECTOR_H_

namespace capd{
namespace vectalg{



/// Intersection of src with target[start..stop] is returned in target
template<typename VectorType1, typename VectorType2>
void intersectionWithSubvector(const VectorType1 & src, VectorType2 & target,
                               int start, int stop);

/// it copies src into target[start..stop]
template<typename VectorType1, typename VectorType2>
void copyToSubvector(const VectorType1 & src,  VectorType2 & target,
                     int start, int stop);

/// it copies src[start..stop] into target
template<typename VectorType1, typename VectorType2>
void copyFromSubvector(const VectorType1& src, VectorType2& target,
                       int start, int stop);



/// intersection of src with target[startRow..stopRow][startCol..stopCol] is returned in target
template<typename MatrixType1, typename MatrixType2>
void intersectionWithSubmatrix( const MatrixType1 & src,
                                MatrixType2 & target,
                                int startRow, int stopRow,
                                int startCol, int stopCol);

/// it copies src into target[startRow..stopRow)[startCol..stopCol)
template<typename MatrixType1, typename MatrixType2>
void copyToSubmatrix(const MatrixType1 & src,
                     MatrixType2 & target,
                     int startRow, int stopRow,
                     int startCol, int stopCol);

/// it copies src[startRow..stopRow)[startCol..stopCol) into target
template<typename MatrixType1, typename MatrixType2>
void copyFromSubmatrix(const MatrixType1 & src,
                       MatrixType2 & target,
                       int startRow, int stopRow,
                       int startCol, int stopCol);

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_SUBVECTOR_H_

/// @}

