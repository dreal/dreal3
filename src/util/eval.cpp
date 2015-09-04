/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include "util/eval.h"

#include <cmath>
#include <exception>
#include <iostream>
#include "./nlopt.hpp"

using std::cerr;
using std::cout;
using std::endl;
using std::runtime_error;
using std::unordered_map;

namespace dreal {

double eval_enode(Enode * const e, unordered_map<Enode*, double> const & var_map) {
    if (e->isVar()) {
        auto const it = var_map.find(e);
        if (it == var_map.cend()) {
            throw runtime_error("variable not found");
        } else {
            // Variable is found in var_map
            return it->second;
        }
    } else if (e->isConstant()) {
        double const v = e->getValue();
        return v;
    } else if (e->isSymb()) {
        throw runtime_error("eval_enode: Symb");
    } else if (e->isNumb()) {
        throw runtime_error("eval_enode: Numb");
    } else if (e->isTerm()) {
        assert(e->getArity() >= 1);
        enodeid_t id = e->getCar()->getId();
        double ret = 0.0;
        Enode * tmp = e;
        switch (id) {
        case ENODE_ID_PLUS:
            ret = eval_enode(tmp->get1st(), var_map);
            tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!tmp->isEnil()) {
                ret = ret + eval_enode(tmp->getCar(), var_map);
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_MINUS:
            ret = eval_enode(tmp->get1st(), var_map);
            tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!tmp->isEnil()) {
                ret = ret - eval_enode(tmp->getCar(), var_map);
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_UMINUS:
            ret = eval_enode(tmp->get1st(), var_map);
            assert(tmp->getArity() == 1);
            return (- ret);
        case ENODE_ID_TIMES:
            ret = eval_enode(tmp->get1st(), var_map);
            tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!tmp->isEnil()) {
                ret = ret * eval_enode(tmp->getCar(), var_map);
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_DIV:
            ret = eval_enode(tmp->get1st(), var_map);
            tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!tmp->isEnil()) {
                ret = ret / eval_enode(tmp->getCar(), var_map);
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_ACOS:
            assert(e->getArity() == 1);
            return acos(eval_enode(e->get1st(), var_map));
        case ENODE_ID_ASIN:
            assert(e->getArity() == 1);
            return asin(eval_enode(e->get1st(), var_map));
        case ENODE_ID_ATAN:
            assert(e->getArity() == 1);
            return atan(eval_enode(e->get1st(), var_map));
        case ENODE_ID_ATAN2:
            assert(e->getArity() == 2);
            return atan2(eval_enode(e->get1st(), var_map),
                         eval_enode(e->get2nd(), var_map));
        case ENODE_ID_MIN:
            assert(e->getArity() == 2);
            return fmin(eval_enode(e->get1st(), var_map),
                        eval_enode(e->get2nd(), var_map));
        case ENODE_ID_MAX:
            assert(e->getArity() == 2);
            return fmax(eval_enode(e->get1st(), var_map),
                        eval_enode(e->get2nd(), var_map));
        case ENODE_ID_MATAN:
            // TODO(soonhok): MATAN
            throw runtime_error("eval_enode: MATAN");
        case ENODE_ID_SAFESQRT:
            // TODO(soonhok): SAFESQRT
            throw runtime_error("eval_enode: SAFESQRT");
        case ENODE_ID_SQRT:
            assert(e->getArity() == 1);
            return sqrt(eval_enode(e->get1st(), var_map));
        case ENODE_ID_EXP:
            assert(e->getArity() == 1);
            return exp(eval_enode(e->get1st(), var_map));
        case ENODE_ID_LOG:
            assert(e->getArity() == 1);
            return log(eval_enode(e->get1st(), var_map));
        case ENODE_ID_POW:
            assert(e->getArity() == 2);
            return pow(eval_enode(e->get1st(), var_map),
                       eval_enode(e->get2nd(), var_map));
        case ENODE_ID_ABS:
            assert(e->getArity() == 1);
            return fabs(eval_enode(e->get1st(), var_map));
        case ENODE_ID_SIN:
            assert(e->getArity() == 1);
            return sin(eval_enode(e->get1st(), var_map));
        case ENODE_ID_COS:
            assert(e->getArity() == 1);
            return cos(eval_enode(e->get1st(), var_map));
        case ENODE_ID_TAN:
            assert(e->getArity() == 1);
            return tan(eval_enode(e->get1st(), var_map));
        case ENODE_ID_SINH:
            assert(e->getArity() == 1);
            return sinh(eval_enode(e->get1st(), var_map));
        case ENODE_ID_COSH:
            assert(e->getArity() == 1);
            return cosh(eval_enode(e->get1st(), var_map));
        case ENODE_ID_TANH:
            assert(e->getArity() == 1);
            return tanh(eval_enode(e->get1st(), var_map));
        default:
            throw runtime_error("eval_enode: Unknown Term");
        }
    } else if (e->isList()) {
        throw runtime_error("eval_enode: List");
    } else if (e->isDef()) {
        throw runtime_error("eval_enode: Def");
    } else if (e->isEnil()) {
        throw runtime_error("eval_enode: Nil");
    } else {
        throw runtime_error("eval_enode: unknown case");
    }
    throw runtime_error("Not implemented yet: eval_enode");
}

}  // namespace dreal
