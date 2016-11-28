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

#include "tools/dop/print_latex.h"

#include <assert.h>       // for assert
#include <functional>     // for __base, function
#include <stdexcept>      // for runtime_error
#include <string>         // for allocator, operator+, basic_string
#include <unordered_map>  // for unordered_map

#include "egraph/Enode.h"     // for Enode, operator<<
#include "tools/dop/print.h"  // for print_call_paren, print_call_brace

namespace dop {

using std::ostream;
using std::string;
using std::unordered_map;
using std::ostringstream;
using std::runtime_error;

ostream & print_latex_infix_op(ostream & out, Enode * const e, string const & op,
                               std::function<ostream &(ostream &, Enode * const)> const & f) {
    assert(e->getArity() >= 2);
    out << "{";
    f(out, e->get1st());
    Enode * tmp = e->getCdr()->getCdr();
    while (!tmp->isEnil()) {
        out << "} " << op << " {";
        f(out, tmp->getCar());
        tmp = tmp->getCdr();
    }
    out << "}";
    return out;
}

ostream & print_latex_infix(ostream & out, Enode * const e) {
    if (e->isSymb()) {
        out << e;
    } else if (e->isNumb()) {
        out << e;
    } else if (e->isVar()) {
        out << e;
    } else if (e->isTerm()) {
        if (e->isPlus()) {
            print_latex_infix_op(out, e, "+", print_latex_infix);
        } else if (e->isMinus()) {
            print_latex_infix_op(out, e, "-", print_latex_infix);
        } else if (e->isTimes()) {
            print_latex_infix_op(out, e, "*", print_latex_infix);
        } else if (e->isDiv()) {
            print_latex_infix_op(out, e, "/", print_latex_infix);
        } else if (e->isPow()) {
            print_latex_infix_op(out, e, "^", print_latex_infix);
        } else if (e->isAbs()) {
            print_call_bar(out, e, "", print_latex_infix);
        } else if (e->isSin()) {
            print_call_paren(out, e, "\\sin", print_latex_infix);
        } else if (e->isCos()) {
            print_call_paren(out, e, "\\cos", print_latex_infix);
        } else if (e->isTan()) {
            print_call_paren(out, e, "\\tan", print_latex_infix);
        } else if (e->isAsin()) {
            print_call_paren(out, e, "\\arcsin", print_latex_infix);
        } else if (e->isAcos()) {
            print_call_paren(out, e, "\\arccos", print_latex_infix);
        } else if (e->isAtan()) {
            print_call_paren(out, e, "\\arctan", print_latex_infix);
        } else if (e->isLog()) {
            print_call_paren(out, e, "\\log", print_latex_infix);
        } else if (e->isExp()) {
            print_call_brace(out, e, "e^", print_latex_infix);
        } else if (e->isSqrt()) {
            print_call_brace(out, e, "\\sqrt", print_latex_infix);
        } else if (e->isAtan2()) {
            print_call_paren(out, e, "\\arctan2", print_latex_infix);
        } else {
            out << e;
        }
    } else if (e->isList()) {
        ostringstream ss;
        ss << e;
        throw std::runtime_error("List " + ss.str() +
                                 " doesn't have a mapping in print_latex_infix");
    } else if (e->isDef()) {
        ostringstream ss;
        ss << e;
        throw std::runtime_error("Def " + ss.str() +
                                 " doesn't have a mapping in print_latex_infix");
    } else if (e->isEnil()) {
        ostringstream ss;
        ss << e;
        throw std::runtime_error("Enil " + ss.str() +
                                 " doesn't have a mapping in print_latex_infix");
    } else {
        ostringstream ss;
        ss << e;
        throw std::runtime_error("Unknown enode " + ss.str() +
                                 " doesn't have a mapping in print_latex_infix");
    }
    return out;
}

}  // namespace dop
