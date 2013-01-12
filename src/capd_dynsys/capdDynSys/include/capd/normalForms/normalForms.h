/// @addtogroup normalForms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file normalForms.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_NORMALFORMS_NORMALFORMS_H_ 
#define _CAPD_NORMALFORMS_NORMALFORMS_H_ 

#include <complex>
#include <stdexcept>
#include <sstream>

#include "capd/map/CnCoeff.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/vectalg/Multiindex.h"

namespace capd{
namespace normalForms{

// -------------------------------------------------------------------------- //

template<typename MatrixType>
void derivativesToSeries(capd::map::CnCoeff< MatrixType >& s)
{
  typedef typename capd::map::CnCoeff< MatrixType >::ScalarType ScalarType;
  for(int i=2;i<=s.rank();++i)
  {
    typename capd::map::CnCoeff< MatrixType >::Multipointer mp = s.first(i);
    do{
     long fac = mp.factorial();
     for(int j=0;j<s.dimension();++j)
     {
       s(j,mp) /= typename capd::TypeTraits<ScalarType>::Real(fac);
     }
    }while(s.next(mp));
  }
}

template<typename MatrixType>
void seriesToDerivatives(capd::map::CnCoeff< MatrixType >& s)
{
  typedef typename capd::map::CnCoeff< MatrixType >::ScalarType ScalarType;
  for(int i=2;i<=s.rank();++i)
  {
    typename capd::map::CnCoeff< MatrixType >::Multipointer mp = s.first(i);
    do{
     long fac = mp.factorial();
     for(int j=0;j<s.dimension();++j)
     {
       s(j,mp) *= typename capd::TypeTraits<ScalarType>::Real(fac);
     }
    }while(s.next(mp));
  }
}

}} // namespace capd::normalForms

#include "capd/normalForms/linearSubstitution.hpp"
#include "capd/normalForms/planarMaps.hpp"

#endif // _CAPD_NORMALFORMS_NORMALFORMS_H_ 

/// @}
