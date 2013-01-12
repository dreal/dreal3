
/////////////////////////////////////////////////////////////////////////////
/// @file ReorganizationPolicy.h
///
/// @author kapela
/// Created on: Oct 23, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_SETDEFAULTREORGANIZATION_H_
#define _CAPD_DYNSET_SETDEFAULTREORGANIZATION_H_

#include "capd/dynset/NoReorganization.h"

namespace capd{
namespace dynset{
// @addtogroup capd
/// @{

/**
 *  General default reorganization do nothing.
 *  But for specific set type it can be specialized.
 */
template <typename SetT>
class ReorganizationPolicy{
public:
   typedef capd::dynset::NoReorganization<SetT>  DefaultReorganization;
};

/// @}
}} // namespace capd::dynset

#endif  //_CAPD_DYNSET_SETDEFAULTREORGANIZATION_H_
