/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file hitenter.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2008 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// This is an extremely simple program which simulates the DOS command pause.
// I have written it just because I don't know what the equivalent of this
// command under Unix is. Silly, isn't it? ;)

// Modified on January 17, 2002, on March 23, 2002, and on February 16, 2003.


#include "capd/homology/timeused.h"

#include <iostream>

using namespace capd::homology;

int main (int argc, char *argv [])
{
	std::cout << "Press ENTER";
	for (int i = 1; i < argc; i ++)
		std::cout << " " << argv [i];
	std::cout << "..." << std::endl;
	while (std::cin. get () != '\n');
	program_time = 0;
	return 0;
} /* main */

/// @}

