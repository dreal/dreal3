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

#include "tools/dop/print_py.h"

#include <functional>
#include <stdexcept>
#include <string>
#include <unordered_map>

#include "opensmt/egraph/Enode.h"
#include "tools/dop/print.h"

namespace dop {

using std::ostream;
using std::string;
using std::unordered_map;
using std::ostringstream;
using std::runtime_error;

ostream & print_py_infix(ostream & out, Enode * const e) {
    if (e->isSymb()) {
        out << e;
    } else if (e->isNumb()) {
        out << e;
    } else if (e->isVar()) {
        out << e;
    } else if (e->isTerm()) {
        if (e->isPlus()) {
            print_infix_op(out, e, "+", print_py_infix);
        } else if (e->isMinus()) {
            print_infix_op(out, e, "-", print_py_infix);
        } else if (e->isTimes()) {
            print_infix_op(out, e, "*", print_py_infix);
        } else if (e->isDiv()) {
            print_infix_op(out, e, "/", print_py_infix);
        } else if (e->isPow()) {
            print_infix_op(out, e, "**", print_py_infix);
        } else if (e->isAbs()) {
            print_call_paren(out, e, "numpy.abs", print_py_infix);
        } else if (e->isSin()) {
            print_call_paren(out, e, "numpy.sin", print_py_infix);
        } else if (e->isCos()) {
            print_call_paren(out, e, "numpy.cos", print_py_infix);
        } else if (e->isTan()) {
            print_call_paren(out, e, "numpy.tan", print_py_infix);
        } else if (e->isAsin()) {
            print_call_paren(out, e, "numpy.asin", print_py_infix);
        } else if (e->isAcos()) {
            print_call_paren(out, e, "numpy.acos", print_py_infix);
        } else if (e->isAtan()) {
            print_call_paren(out, e, "numpy.atan", print_py_infix);
        } else if (e->isLog()) {
            print_call_paren(out, e, "numpy.log", print_py_infix);
        } else if (e->isExp()) {
            print_call_paren(out, e, "numpy.exp", print_py_infix);
        } else if (e->isSqrt()) {
            print_call_paren(out, e, "numpy.sqrt", print_py_infix);
        } else if (e->isAtan2()) {
            print_call_paren(out, e, "numpy.atan2", print_py_infix);
        } else {
            out << e;
        }
    } else if (e->isList()) {
        ostringstream ss;
        ss << e;
        throw std::runtime_error("List " + ss.str() + " doesn't have a mapping in print_py_infix");
    } else if (e->isDef()) {
        ostringstream ss;
        ss << e;
        throw std::runtime_error("Def " + ss.str() + " doesn't have a mapping in print_py_infix");
    } else if (e->isEnil()) {
        ostringstream ss;
        ss << e;
        throw std::runtime_error("Enil " + ss.str() + " doesn't have a mapping in print_py_infix");
    } else {
        ostringstream ss;
        ss << e;
        throw std::runtime_error("Unknown enode " + ss.str() +
                                 " doesn't have a mapping in print_py_infix");
    }
    return out;
}

}  // namespace dop
