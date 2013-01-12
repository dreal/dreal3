/////////////////////////////////////////////////////////////////////////////
//
/// @file integrate.cpp
///
/// @author Daniel Wilczak
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) CAPD group
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.


#include "capd/capdlib.h"

using namespace capd;
using namespace std;

int main()
{
  cout.precision(12);
  try{
    // This is vector field for the Rossler system
    IMap vectorField("par:a,b;var:x,y,z;fun:-(y+z),x+b*y,b+z*(x-a);");

    // set chaotic parameter values
    vectorField.setParameter("a",interval(57.)/10.); // a=5.7
    vectorField.setParameter("b",interval(2.)/10.); // b=0.2

    // the solver, is uses high order enclosure method to verify the existence 
    // of the solution. The order is set to 20.
    // The time step (when step control is turned off) will be 0.1.
    ITaylor solver(vectorField,20,.1);

    ITimeMap timeMap(solver);
    // this is a good approximation of a periodic point
    IVector c(3);
    c[0] = 0.;
    c[1] = -8.3809417428298;
    c[2] = 0.029590060630665;
    // take some box around c
    c += interval(-1,1)*1e-10; 

    // define a doubleton representation of the interval vector c
    C0Rect2Set s(c);

    // we integrate the set s over the time T
    interval T(100);
    
    cout << "\ninitial set: " << c;
    cout << "\ndiam(initial set): " << diam(c) << endl;

    IVector result = timeMap(T,s);

    cout << "\n\nafter time=" << T << " the image is: " << result;
    cout << "\ndiam(image): " << diam(result) << endl << endl;
  }catch(exception& e)
  {
    cout << "\n\nException caught!\n" << e.what() << endl << endl;
  }
} // END
