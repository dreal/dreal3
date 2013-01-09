/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file acyclicConfigs.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_ACYCLICCONFIGSREAD_H_)
#define _ACYCLICCONFIGSREAD_H_

static const unsigned int acyclicConfigsSize = (1 << 23); // 2^26/8 = 8*1024*1024
extern unsigned char *acyclicConfigsD3;

void readAcyclicConfigs();

#endif //_ACYCLICCONFIGSREAD_H_
/// @}

