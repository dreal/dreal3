
/////////////////////////////////////////////////////////////////////////////
/// @file Norm.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/vectalg/mplib.h"
#include "capd/vectalg/Norm.hpp"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"

namespace capd{ 
  namespace vectalg{

#ifdef __HAVE_MPFR__

  template class capd::vectalg::Norm<MpIVector,MpIMatrix>;
  template class capd::vectalg::EuclNorm<MpIVector,MpIMatrix>;
  template class capd::vectalg::MaxNorm<MpIVector,MpIMatrix>;
  template class capd::vectalg::SumNorm<MpIVector,MpIMatrix>;
  template class capd::vectalg::EuclLNorm<MpIVector,MpIMatrix>;
  template class capd::vectalg::MaxLNorm<MpIVector,MpIMatrix>;
  template class capd::vectalg::SumLNorm<MpIVector,MpIMatrix>;

  template class capd::vectalg::Norm<MpVector,MpMatrix>;
  template class capd::vectalg::EuclNorm<MpVector,MpMatrix>;
  template class capd::vectalg::MaxNorm<MpVector,MpMatrix>;
  template class capd::vectalg::SumNorm<MpVector,MpMatrix>;
  template class capd::vectalg::EuclLNorm<MpVector,MpMatrix>;
  template class capd::vectalg::MaxLNorm<MpVector,MpMatrix>;
  template class capd::vectalg::SumLNorm<MpVector,MpMatrix>;


#endif


}}  // end of namespace capd::vectalg

