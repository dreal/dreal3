/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include <string>
#include "ibex/ibex.h"
#include "util/logging.h"
#include "util/ibex_enode.h"

namespace dreal {

using ibex::ExprNode;
using ibex::Variable;
using ibex::ExprConstant;
using ibex::ExprCtr;
using ibex::ExprNode;

ExprNode const * translate_enode_to_exprnode(unordered_map<string, Variable const> & var_map, Enode const * e) {
    // TODO(soonhok): for the simple case such as 0 <= x or x <= 10.
    // Handle it as a domain specification instead of constraints.
    if (e->isVar()) {
        string const & var_name = e->getCar()->getName();
        auto it = var_map.find(var_name);
        if (it == var_map.end()) {
            // The variable is new, we need to make one.
            Variable v(var_name.c_str());
            // double const lb = e->getLowerBound();
            // double const ub = e->getUpperBound();
            var_map.emplace(var_name, v);
            return v.symbol;
        } else {
            // Variable is found in var_map
            Variable const & v = it->second;
            return v.symbol;
        }

    } else if (e->isConstant()) {
        // TODO(soonhok): handle number c as an interval [lb(c), ub(c)]
        return &ExprConstant::new_scalar(e->getValue());
    } else if (e->isSymb()) {
        throw logic_error("translateEnodeExprNode: Symb");
    } else if (e->isNumb()) {
        throw logic_error("translateEnodeExprNode: Numb");
    } else if (e->isTerm()) {
        assert(e->getArity() >= 1);
        ExprNode const * ret = translate_enode_to_exprnode(var_map, e->get1st());
        enodeid_t id = e->getCar()->getId();
        switch (id) {
        case ENODE_ID_PLUS:
            e = e->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!e->isEnil()) {
                ret = &(*ret + *translate_enode_to_exprnode(var_map, e->getCar()));
                e = e->getCdr();
            }
            return ret;
        case ENODE_ID_MINUS:
            e = e->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!e->isEnil()) {
                ret = &(*ret - *translate_enode_to_exprnode(var_map, e->getCar()));
                e = e->getCdr();
            }
            return ret;
        case ENODE_ID_UMINUS:
            assert(e->getArity() == 1);
            return &(- *ret);
        case ENODE_ID_TIMES:
            e = e->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!e->isEnil()) {
                ret = &(*ret * *translate_enode_to_exprnode(var_map, e->getCar()));
                e = e->getCdr();
            }
            return ret;
        case ENODE_ID_DIV:
            e = e->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!e->isEnil()) {
                ret = &(*ret / *translate_enode_to_exprnode(var_map, e->getCar()));
                e = e->getCdr();
            }
            return ret;
        case ENODE_ID_ACOS:
            assert(e->getArity() == 1);
            return &acos(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_ASIN:
            assert(e->getArity() == 1);
            return &asin(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_ATAN:
            assert(e->getArity() == 1);
            return &atan(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_ATAN2:
            assert(e->getArity() == 2);
            return &atan2(*translate_enode_to_exprnode(var_map, e->get1st()), *translate_enode_to_exprnode(var_map, e->get2nd()));
        case ENODE_ID_MATAN:
            // TODO(soonhok): MATAN
            throw logic_error("translateEnodeExprNode: MATAN");
        case ENODE_ID_SAFESQRT:
            // TODO(soonhok): SAFESQRT
            throw logic_error("translateEnodeExprNode: SAFESQRT");
        case ENODE_ID_EXP:
            assert(e->getArity() == 1);
            return &exp(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_LOG:
            assert(e->getArity() == 1);
            return &log(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_POW:
            assert(e->getArity() == 2);
            if (e->get2nd()->isConstant() && e->get2nd()->getValue() == 2) {
                // If x^2, use sqr(x) instead of pow(x, y)
                return &sqr(*translate_enode_to_exprnode(var_map, e->get1st()));
            } else {
                return &pow(*translate_enode_to_exprnode(var_map, e->get1st()), *translate_enode_to_exprnode(var_map, e->get2nd()));
            }
        case ENODE_ID_ABS:
            assert(e->getArity() == 1);
            return &abs(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_SIN:
            assert(e->getArity() == 1);
            return &sin(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_COS:
            assert(e->getArity() == 1);
            return &cos(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_TAN:
            assert(e->getArity() == 1);
            return &tan(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_SINH:
            assert(e->getArity() == 1);
            return &sinh(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_COSH:
            assert(e->getArity() == 1);
            return &cosh(*translate_enode_to_exprnode(var_map, e->get1st()));
        case ENODE_ID_TANH:
            assert(e->getArity() == 1);
            return &tanh(*translate_enode_to_exprnode(var_map, e->get1st()));
        default:
            throw logic_error("translateEnodeExprNode: Unknown Term");
        }
    } else if (e->isList()) {
        throw logic_error("translateEnodeExprNode: List");
    } else if (e->isDef()) {
        throw logic_error("translateEnodeExprNode: Def");
    } else if (e->isEnil()) {
        throw logic_error("translateEnodeExprNode: Nil");
    } else {
        throw logic_error("translateEnodeExprNode: unknown case");
    }
    throw logic_error("Not implemented yet: translateEnodeExprNode");
}

ExprCtr const * translate_enode_to_exprctr(unordered_map<string, Variable const> & var_map, Enode const * e) {
    assert(e->isTerm() && (e->isEq() || e->isLeq() || e->isGeq() || e->isLt() || e->isGt()));

    // Enode const * const rel = e->getCar();
    Enode const * const first_op = e->get1st();
    Enode const * const second_op = e->get2nd();

    ExprNode const * left = translate_enode_to_exprnode(var_map, first_op);
    ExprNode const * right = translate_enode_to_exprnode(var_map, second_op);
    auto const polarity = e->getPolarity();
    switch (e->getCar()->getId()) {
    case ENODE_ID_EQ:
        // TODO(soonhok): remove != case
        return (polarity == l_True) ? &(*left =  *right) : nullptr;
    case ENODE_ID_LEQ:
        return (polarity == l_True) ? &(*left <= *right) : &(*left >  *right);
    case ENODE_ID_GEQ:
        return (polarity == l_True) ? &(*left >= *right) : &(*left <= *right);
    case ENODE_ID_LT:
        return (polarity == l_True) ? &(*left <  *right) : &(*left >  *right);
    case ENODE_ID_GT:
        return (polarity == l_True) ? &(*left >  *right) : &(*left <  *right);
    default:
        throw logic_error("translate_enode_to_exprctr: default");
    }
    throw logic_error("Not implemented yet: translate_enode_to_exprctr");
}
}  // namespace dreal
