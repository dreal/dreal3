/*                                                                           
**  fi_lib++  --- A fast interval library (Version 2.0)                     
**                                                                  
**  Copyright (C) 2001:                                                        
**                                                     
**  Werner Hofschuster, Walter Kraemer                               
**  Wissenschaftliches Rechnen/Softwaretechnologie (WRSWT)  
**  Universitaet Wuppertal, Germany                                           
**  Michael Lerch, German Tischler, Juergen Wolff von Gudenberg       
**  Institut fuer Informatik                                         
**  Universitaet Wuerzburg, Germany                                           
** 
**  This library is free software; you can redistribute it and/or
**  modify it under the terms of the GNU Library General Public
**  License as published by the Free Software Foundation; either
**  version 2 of the License, or (at your option) any later version.
**
**  This library is distributed in the hope that it will be useful,
**  but WITHOUT ANY WARRANTY; without even the implied warranty of
**  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
**  Library General Public License for more details.
**
**  You should have received a copy of the GNU Library General Public
**  License along with this library; if not, write to the Free
**  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
*/
#include <fstream>
#include <iomanip>
#include <string>
#include "config.h"

extern char* in_no[27][61];
extern char* out_no[27][61];

void initStdFunTestCases();

/** uses test set of original fi_lib as bases
 ** code partially from fi_test.c **/

typedef union { double r; char a[7]; } twoint;

twoint trick;

#if (BYTE_ORDER == LITTLE_ENDIAN)
	int wks = 2;
#else
	int wks = 1;
#endif 

int alltrue=1;

char hexr(char const *b,int const & i)
{
	int j;
	int k;
	char erg, rueck;

	erg=*(b+(2*i-2));

	switch (erg)
	{ 
		case 'A': k=10; break;
		case 'B': k=11; break;
		case 'C': k=12; break;
		case 'D': k=13; break;
		case 'E': k=14; break;
		case 'F': k=15; break;
		default:k=erg-48;
	}

	k=k*16;
	erg=*(b+(2*i-1));

	switch (erg)
	{
		case 'A': j=10; break;
		case 'B': j=11; break;
		case 'C': j=12; break;
		case 'D': j=13; break;
		case 'E': j=14; break;
		case 'F': j=15; break;
		default:j=erg-48;
	}

	k=k+j;
	rueck=k;
	return rueck;
}

double hexu(char * const b)
{
	int i;

	for (i=1;i<=8;i++) 
	{
		if (wks==1) trick.a[i-1]=hexr(b,i);
		if (wks==2) trick.a[i-1]=hexr(b,9-i);
	}

	return trick.r;
}

#include "makeTestCases.icc"

void executeTest()
{
	if (!filib::interval<double,filib::native_switched,filib::i_mode_extended>::isExtended()) 
	{
		std::cout << "ERROR: makeTestCases must be run in extended mode !" << std::endl;
		exit(-1);
	}
  
	filib::interval<double,filib::native_switched,filib::i_mode_extended>::precision(10);

	std::ofstream out;
	out.open("testSet.cpp");
	out << "#include \"config.h\"" << std::endl;
	out << "#include \"tsPredSucc.cpp\"" << std::endl;
	out << "#include \"tsBounds.cpp\"" << std::endl;
	out << "#include \"tsInfo.cpp\"" << std::endl;
	out << "#include \"tsUtil.cpp\"" << std::endl;
	out << "#include \"tsSetOp.cpp\"" << std::endl;
	out << "#include \"tsAri.cpp\"" << std::endl;
	out << "#include \"tsStdFun.cpp\"" << std::endl;
	out << std::endl;

	size_t n = commonIntvTestSet_size();

	printTestSetSize("ci", n, citsExtendedCases, out);

	printTestSet("ciTestSet", n, 
		citsExtendedCases, 
		commonIntvTestSet, out);
	
	n = setRelTestSet1_size();

	printTestSetSize("sr", n, srtsExtendedCases, out);
	printTestSet("srTestSet1", n, srtsExtendedCases, setRelTestSet1, out);
	printTestSet("srTestSet2", n, srtsExtendedCases, setRelTestSet2, out);

	out.close();

	out.open("tsPredSucc.cpp");
	makePredSuccTestSet(out);
	out.close();

	out.open("tsBounds.cpp");
	makeBoundsTestSet(out);  
	out.close();

	out.open("tsInfo.cpp");
	makeInfoTestSet(out);
	out.close();

	out.open("tsUtil.cpp");
	makeUtilTestSet(out);  
	out.close();

	out.open("tsSetOp.cpp");
	makeSetOpTestSet(out);  
	out.close();

	out.open("tsAri.cpp");
	makeAriTestSet(out);  
	out.close();

	out.open("tsStdFun.cpp");
	makeStdFunTestSet(out);  
	out.close();
}

int main() 
{
	filib::fp_traits<double,filib::native_switched>::setup();
	setup_sets();
	executeTest();
	return 0;
}
