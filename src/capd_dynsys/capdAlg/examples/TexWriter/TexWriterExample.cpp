//////////////////////////////////////////////////////////////////////////////
///
///  @file TexWriterExample.cpp
///  
///  Example how to use TexWriter class.
///
///  Compile and run:
///    - make
///    - ./TexWriterExample
///
///  @author kapela  @date   Mar 30, 2011
//////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2011 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#include "capd/basicalg/TexWriter.h"
#include <iostream>
#include <iomanip>
#include <fstream>
#include "capd/capdAlglib.h"
using namespace std;
using namespace capd;

int main(int argc, char **argv) {

#ifdef __USE_FILIB__
  Interval::precision(16);
#endif
  // TexWriter that will write to screen

  TexWriter out(cout);
  cout.precision(16);
  Interval x("11244.52423323212323423","11244.5242532232234324");
  cout <<"\nInterval  : " << x << "\n can be written in TeX form as " << std::endl;

  out.precision(10);
  out.setFloatStyle(TexWriter::FloatSci).setBaseStyle(0);
  out << "Sci  0    : " << x  << std::endl;

  out.setBaseStyle(1);
  out << "Sci  1    : " << x  << std::endl;

  out.setFloatStyle(TexWriter::FloatFix);
  out << "Fix       : " << x << std::endl;

  out.setFloatStyle(TexWriter::FloatFix2);
  out << "Fix2      : " << x << std::endl;

  return 0;
}
