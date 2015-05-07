#include <iostream>
#include "ibex/ibex.h"

using namespace ibex;
using std::cout;
using std::endl;

int main() {
    // z = atan2(y, x)
    Variable x, y, z;
    Function f(y, x, z, z - atan2(y, x));
    NumConstraint c(f);
    CtcFwdBwd ctc(c);

    IntervalVector box(3);
    box[0] = Interval(1,1);
    box[1] = Interval(0,0);
    box[2] = Interval(-100,100);

    cout << "Before contract: " << box << endl;
    ctc.contract(box);
    cout << "After contract: " << box << endl;
    return 0;
}
