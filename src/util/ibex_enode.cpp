/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

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

#include <algorithm>
#include <cmath>
#include <limits>
#include <string>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include "ibex/ibex.h"
#include "util/logging.h"
#include "util/ibex_enode.h"

namespace dreal {

using ibex::ExprConstant;
using ibex::ExprCtr;
using ibex::ExprNode;
using ibex::ExprNode;
using ibex::Variable;
using std::logic_error;
using std::map;
using std::modf;
using std::numeric_limits;
using std::string;
using std::unordered_map;
using std::unordered_set;

// Translate an Enode e into ibex::ExprNode.
// Note: As a side-effect, update var_map : string -> ibex::Variable
// Note: Use subst map (Enode ->ibex::Interval)
ExprNode const * translate_enode_to_exprnode(map<string, Variable const> & var_map, Enode * const e, unordered_map<Enode*, ibex::Interval> const & subst) {
    // TODO(soonhok): for the simple case such as 0 <= x or x <= 10.
    // Handle it as a domain specification instead of constraints.
    if (e->isVar()) {
        auto const subst_it = subst.find(e);
        if (subst_it != subst.cend()) {
            auto const i = subst_it->second;
            return &ExprConstant::new_scalar(i);
        }
        string const & var_name = e->getCar()->getName();
        auto const it = var_map.find(var_name);
        if (it == var_map.cend()) {
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
        double const v = e->getValue();
        if (v == +numeric_limits<double>::infinity()) {
            return &ExprConstant::new_scalar(ibex::Interval(numeric_limits<double>::max(), v));
        } else if (v == -numeric_limits<double>::infinity()) {
            return &ExprConstant::new_scalar(ibex::Interval(v, numeric_limits<double>::lowest()));
        } else {
            return &ExprConstant::new_scalar(v);
        }
    } else if (e->isSymb()) {
        throw logic_error("translateEnodeExprNode: Symb");
    } else if (e->isNumb()) {
        throw logic_error("translateEnodeExprNode: Numb");
    } else if (e->isTerm()) {
        assert(e->getArity() >= 1);
        enodeid_t id = e->getCar()->getId();
        ExprNode const * ret = nullptr;
        Enode * tmp = e;
        switch (id) {
        case ENODE_ID_PLUS:
            ret = translate_enode_to_exprnode(var_map, tmp->get1st(), subst);
            tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!tmp->isEnil()) {
                ret = &(*ret + *translate_enode_to_exprnode(var_map, tmp->getCar(), subst));
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_MINUS:
            ret = translate_enode_to_exprnode(var_map, tmp->get1st(), subst);
            tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!tmp->isEnil()) {
                ret = &(*ret - *translate_enode_to_exprnode(var_map, tmp->getCar(), subst));
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_UMINUS:
            ret = translate_enode_to_exprnode(var_map, tmp->get1st(), subst);
            assert(tmp->getArity() == 1);
            return &(- *ret);
        case ENODE_ID_TIMES:
            ret = translate_enode_to_exprnode(var_map, tmp->get1st(), subst);
            tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!tmp->isEnil()) {
                ret = &(*ret * *translate_enode_to_exprnode(var_map, tmp->getCar(), subst));
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_DIV:
            ret = translate_enode_to_exprnode(var_map, tmp->get1st(), subst);
            tmp = tmp->getCdr()->getCdr();  // e is pointing to the 2nd arg
            while (!tmp->isEnil()) {
                ret = &(*ret / *translate_enode_to_exprnode(var_map, tmp->getCar(), subst));
                tmp = tmp->getCdr();
            }
            return ret;
        case ENODE_ID_ACOS:
            assert(e->getArity() == 1);
            return &acos(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_ASIN:
            assert(e->getArity() == 1);
            return &asin(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_ATAN:
            assert(e->getArity() == 1);
            return &atan(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_ATAN2:
            assert(e->getArity() == 2);
            return &atan2(*translate_enode_to_exprnode(var_map, e->get1st(), subst), *translate_enode_to_exprnode(var_map, e->get2nd(), subst));
        case ENODE_ID_MIN:
            assert(e->getArity() == 2);
            return &min(*translate_enode_to_exprnode(var_map, e->get1st(), subst), *translate_enode_to_exprnode(var_map, e->get2nd(), subst));
        case ENODE_ID_MAX:
            assert(e->getArity() == 2);
            return &max(*translate_enode_to_exprnode(var_map, e->get1st(), subst), *translate_enode_to_exprnode(var_map, e->get2nd(), subst));
        case ENODE_ID_MATAN:
            // TODO(soonhok): MATAN
            throw logic_error("translateEnodeExprNode: MATAN");
        case ENODE_ID_SAFESQRT:
            // TODO(soonhok): SAFESQRT
            throw logic_error("translateEnodeExprNode: SAFESQRT");
        case ENODE_ID_SQRT:
            assert(e->getArity() == 1);
            return &sqrt(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_EXP:
            assert(e->getArity() == 1);
            return &exp(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_LOG:
            assert(e->getArity() == 1);
            return &log(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_POW: {
            assert(e->getArity() == 2);
            bool   is_1st_constant = false;
            bool   is_1st_int      = false;
            bool   is_2nd_constant = false;
            bool   is_2nd_int      = false;
            double dbl_1st = 0.0;
            int    int_1st = 0;
            double dbl_2nd = 0.0;
            int    int_2nd = 0;
            if (e->get1st()->isConstant()) {
                dbl_1st = e->get1st()->getValue();
                is_1st_constant = true;
                double tmp;
                if (modf(dbl_1st, &tmp) == 0.0) {
                    is_1st_int = true;
                    int_1st = static_cast<int>(tmp);
                }
            }
            if (e->get2nd()->isConstant()) {
                dbl_2nd = e->get2nd()->getValue();
                is_2nd_constant = true;
                double tmp;
                if (modf(dbl_2nd, &tmp) == 0.0) {
                    is_2nd_int = true;
                    int_2nd = static_cast<int>(tmp);
                }
            }
            if (is_1st_constant && is_2nd_constant) {
                // Both of them are constant, just compute and return a number
                return &ExprConstant::new_scalar(pow(dbl_1st, dbl_2nd));
            }
            // Now, either of them is non-constant.
            if (is_1st_int) {
                return &pow(int_1st, *translate_enode_to_exprnode(var_map, e->get2nd(), subst));
            }
            if (is_1st_constant) {
                return &pow(dbl_1st, *translate_enode_to_exprnode(var_map, e->get2nd(), subst));
            }
            if (is_2nd_int) {
                return &pow(*translate_enode_to_exprnode(var_map, e->get1st(), subst), int_2nd);
            }
            if (is_2nd_constant) {
                return &pow(*translate_enode_to_exprnode(var_map, e->get1st(), subst), dbl_2nd);
            }
            return &pow(*translate_enode_to_exprnode(var_map, e->get1st(), subst), *translate_enode_to_exprnode(var_map, e->get2nd(), subst));
        }
        case ENODE_ID_ABS:
            assert(e->getArity() == 1);
            return &abs(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_SIN:
            assert(e->getArity() == 1);
            return &sin(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_COS:
            assert(e->getArity() == 1);
            return &cos(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_TAN:
            assert(e->getArity() == 1);
            return &tan(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_SINH:
            assert(e->getArity() == 1);
            return &sinh(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_COSH:
            assert(e->getArity() == 1);
            return &cosh(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
        case ENODE_ID_TANH:
            assert(e->getArity() == 1);
            return &tanh(*translate_enode_to_exprnode(var_map, e->get1st(), subst));
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

// Translate an Enode e into ibex::ExprCtr.
// Note: As a side-effect, update var_map : string -> ibex::Variable
// Note: Use subst map (Enode ->ibex::Interval)
ExprCtr const * translate_enode_to_exprctr(map<string, Variable const> & var_map, Enode * const e, lbool p, unordered_map<Enode*, ibex::Interval> const & subst) {
    assert(e->isTerm() && (e->isEq() || e->isLeq() || e->isGeq() || e->isLt() || e->isGt()));

    Enode * const first_op = e->get1st();
    Enode * const second_op = e->get2nd();
    ExprCtr const * ret = nullptr;

    ExprNode const * left = nullptr;
    ExprNode const * right = nullptr;
    bool const is_right_zero = second_op->isConstant() && second_op->getValue() == 0.0;
    if (is_right_zero) {
        right = &ExprConstant::new_scalar(0.0);
    }

    auto const polarity = p == l_Undef ? e->getPolarity() : p;
    switch (e->getCar()->getId()) {
    case ENODE_ID_EQ: {
        // Create "left = right" for both of equality(==) and non-equality cases(!=)
        left = translate_enode_to_exprnode(var_map, first_op, subst);
        if (!is_right_zero) {
            right = translate_enode_to_exprnode(var_map, second_op, subst);
        }
        ret = &(*left = *right);
        break;
    }
    case ENODE_ID_LEQ:
        left = translate_enode_to_exprnode(var_map, first_op, subst);
        if (!is_right_zero) {
            right = translate_enode_to_exprnode(var_map, second_op, subst);
        }
        ret = (polarity == l_True) ? &(*left <= *right) : &(*left >  *right);
        break;
    case ENODE_ID_GEQ:
        left = translate_enode_to_exprnode(var_map, first_op, subst);
        if (!is_right_zero) {
            right = translate_enode_to_exprnode(var_map, second_op, subst);
        }
        ret = (polarity == l_True) ? &(*left >= *right) : &(*left < *right);
        break;
    case ENODE_ID_LT:
        left = translate_enode_to_exprnode(var_map, first_op, subst);
        if (!is_right_zero) {
            right = translate_enode_to_exprnode(var_map, second_op, subst);
        }
        ret = (polarity == l_True) ? &(*left <  *right) : &(*left >=  *right);
        break;
    case ENODE_ID_GT:
        left = translate_enode_to_exprnode(var_map, first_op, subst);
        if (!right) {
            right = translate_enode_to_exprnode(var_map, second_op, subst);
        }
        ret = (polarity == l_True) ? &(*left >  *right) : &(*left <=  *right);
        break;
    default:
        throw logic_error("translate_enode_to_exprctr: default");
    }
    if (is_right_zero) {
        delete right;
    }
    return ret;
}

map<string, Variable const> build_var_map(unordered_set<Enode *> const & vars) {
    map<string, Variable const> var_map;
    for (Enode * const e : vars) {
        string const & var_name = e->getCar()->getName();
        Variable v(var_name.c_str());
        var_map.emplace(var_name, v);
    }
    return var_map;
}

}  // namespace dreal
