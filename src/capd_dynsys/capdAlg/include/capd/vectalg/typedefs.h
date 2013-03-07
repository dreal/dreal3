//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file vectalg/typedefs.h
///
/// @author Daniel Wilczak   @date 2013-01-09
//
/////////////////////////////////////////////////////////////////////////////

// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef CAPD_DEFAULT_DIMENSION
#error "Define macro CAPD_DEFAULT_DIMENSION before including capd/vectalg/typedefs.h"
#endif

#ifndef CAPD_USER_NAMESPACE
#error "Define macro CAPD_USER_NAMESPACE before including capd/vectalg/typedefs.h"
#endif

namespace CAPD_USER_NAMESPACE{
typedef capd::vectalg::Vector<int,CAPD_DEFAULT_DIMENSION> ZVector;

typedef capd::vectalg::Vector<double,CAPD_DEFAULT_DIMENSION> DVector;
typedef capd::vectalg::Matrix<double,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> DMatrix;

typedef capd::vectalg::Vector<capd::DInterval,CAPD_DEFAULT_DIMENSION> IVector;
typedef capd::vectalg::Matrix<capd::DInterval,CAPD_DEFAULT_DIMENSION,CAPD_DEFAULT_DIMENSION> IMatrix;

typedef capd::vectalg::Norm<DVector,DMatrix> DNorm;
typedef capd::vectalg::EuclNorm<DVector,DMatrix> DEuclNorm;
typedef capd::vectalg::MaxNorm<DVector,DMatrix> DMaxNorm;
typedef capd::vectalg::SumNorm<DVector,DMatrix> DSumNorm;
typedef capd::vectalg::EuclLNorm<DVector,DMatrix> DEuclLNorm;
typedef capd::vectalg::MaxLNorm<DVector,DMatrix> DMaxLNorm;
typedef capd::vectalg::SumLNorm<DVector,DMatrix> DSumLNorm;

typedef capd::vectalg::Norm<IVector,IMatrix> INorm;
typedef capd::vectalg::EuclNorm<IVector,IMatrix> IEuclNorm;
typedef capd::vectalg::MaxNorm<IVector,IMatrix> IMaxNorm;
typedef capd::vectalg::SumNorm<IVector,IMatrix> ISumNorm;
typedef capd::vectalg::EuclLNorm<IVector,IMatrix> IEuclLNorm;
typedef capd::vectalg::MaxLNorm<IVector,IMatrix> IMaxLNorm;
typedef capd::vectalg::SumLNorm<IVector,IMatrix> ISumLNorm;

typedef capd::vectalg::Multiindex Multiindex;
typedef capd::vectalg::Multipointer Multipointer;

} // end of the namespace
