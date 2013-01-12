
/////////////////////////////////////////////////////////////////////////////
/// @file Mapping.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_NEWTON_MAPPING_H_ 
#define _CAPD_NEWTON_MAPPING_H_ 

namespace capd{
namespace newton{

///  General function for Newton or Krawczyk method
///  f:R^n -> R^n

template <typename MatrixType>
class Mapping{

  public:
    typedef typename MatrixType::RowVectorType VectorType;

    // value of Function
    virtual typename MatrixType::RowVectorType operator()(const VectorType & X) = 0;

    // computes derivative  of a Function
    virtual MatrixType operator[](const VectorType & X) = 0;

    // value and derivative of a Function
    virtual typename MatrixType::RowVectorType operator()(const VectorType & X, MatrixType &dF) = 0;

    virtual int dimension() = 0;

    virtual ~Mapping() {}
};

}} //end of namespace capd::newton


#endif // _CAPD_NEWTON_MAPPING_H_ 
