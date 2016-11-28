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

#include "tools/dop/print.h"

#include <assert.h>    // for assert
#include <functional>  // for function
#include <iostream>    // for ostream, operator<<, string, basic...
#include <string>

#include "opensmt/egraph/Enode.h"  // for Enode

namespace dop {

using std::ostream;
using std::string;
using std::function;

ostream & print_infix_op(ostream & out, Enode * const e, string const & op,
                         std::function<ostream &(ostream &, Enode * const)> const & f) {
    assert(e->getArity() >= 2);
    out << "(";
    f(out, e->get1st());
    Enode * tmp = e->getCdr()->getCdr();
    while (!tmp->isEnil()) {
        out << " " << op << " ";
        f(out, tmp->getCar());
        tmp = tmp->getCdr();
    }
    out << ")";
    return out;
}

ostream & print_call(ostream & out, Enode * const e, string const & fname,
                     std::function<ostream &(ostream &, Enode * const)> const & f,
                     string const & lp, string const & rp) {
    assert(e->getArity() >= 1);
    out << fname;
    out << lp;
    f(out, e->get1st());
    Enode * tmp = e->getCdr()->getCdr();
    while (!tmp->isEnil()) {
        out << ", ";
        f(out, tmp->getCar());
        tmp = tmp->getCdr();
    }
    out << rp;
    return out;
}

ostream & print_call_bar(ostream & out, Enode * const e, string const & fname,
                         std::function<ostream &(ostream &, Enode * const)> const & f) {
    return print_call(out, e, fname, f, "\\|", "\\|");
}

ostream & print_call_brace(ostream & out, Enode * const e, string const & fname,
                           std::function<ostream &(ostream &, Enode * const)> const & f) {
    return print_call(out, e, fname, f, "{", "}");
}

ostream & print_call_paren(ostream & out, Enode * const e, string const & fname,
                           std::function<ostream &(ostream &, Enode * const)> const & f) {
    return print_call(out, e, fname, f, "(", ")");
}

}  // namespace dop
