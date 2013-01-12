/// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file debuger.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#define TRACE(ARG) std::cout << #ARG << endl; ARG
#undef OUT
#define OUT(X) " " << #X << "= " << X
#define COUT(X) std::cout << #X << "= " << X << std::endl;

/// @}
