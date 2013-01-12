/////////////////////////////////////////////////////////////////////////////
/// @file DInterval.h
///
/// @author kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

// Created on 4 maj 2008, 07:44

#ifndef _CAPD_FACADE_DINTERVAL_H_
#define _CAPD_FACADE_DINTERVAL_H_

#ifndef __USE_FILIB__

#include "capd/intervals/DoubleInterval.h"
namespace capd{
namespace facade{

typedef capd::intervals::DoubleInterval interval;
typedef capd::intervals::DoubleInterval DInterval;

}} // end of namespace capd::facade

#else

#include "capd/filib/Interval.h"
namespace capd{
namespace facade{

typedef ::capd::filib::Interval<double, ::filib::native_directed, ::filib::i_mode_normal >  DInterval;
typedef DInterval interval;

}} // end of namespace capd::facade

#endif

#endif // _CAPD_FACADE_DINTERVAL_H_
