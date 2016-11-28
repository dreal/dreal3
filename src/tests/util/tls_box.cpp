/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include <iostream>
#include <vector>

#include "ibex_Interval.h"
#include "opensmt/api/OpenSMTContext.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/thread_local.h"

class Snode;

using std::cerr;
using std::endl;
using std::vector;

void tls_fun(dreal::box & b) {
    DREAL_THREAD_LOCAL static dreal::box old_box(b);
    DREAL_THREAD_LOCAL static ibex::Interval old_iv(b[0]);
    old_box = b;
    old_iv = b[0];
    // cerr << old_box << endl;
    // cerr << old_iv << endl;
}

int main() {
    auto context = OpenSMTContext();
    Snode * real_sort = context.mkSortReal();
    context.DeclareFun("x", real_sort);
    context.DeclareFun("y", real_sort);
    context.DeclareFun("z", real_sort);

    auto x = context.mkVar("x");
    auto y = context.mkVar("y");
    auto z = context.mkVar("z");
    x->setDomainLowerBound(3);
    x->setDomainUpperBound(5);
    vector<Enode *> vars{x, y, z};
    dreal::box b1(vars);

    tls_fun(b1);

    return 0;
}
