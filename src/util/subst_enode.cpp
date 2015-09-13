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

#include <exception>
#include <unordered_map>
#include <iostream>
#include <sstream>
#include "opensmt/egraph/Enode.h"
#include "util/subst_enode.h"

namespace dreal {
using std::unordered_map;
using std::cerr;
using std::cout;
using std::endl;
using std::ostringstream;

Enode * subst(OpenSMTContext & ctx, Enode * e, unordered_map<Enode *, Enode *> const & m) {
    if (e->isSymb()) {
        return e;
    } else if (e->isNumb()) {
        return e;
    } else if (e->isTerm() && e->isVar()) {
        auto it = m.find(e);
        if (it != m.end()) {
            return it->second;
        } else {
            ostringstream ss;
            ss << e;
            throw std::runtime_error("Variable " + ss.str() + " doesn't have a mapping in subst_map");
        }
    } else if (e->isTerm() && e->getCar()->isNumb()) {
        return e;
    } else if (e->isTerm()) {
        if (e->isPlus()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * const res = ctx.mkPlus(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isMinus()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * const res = ctx.mkMinus(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isTimes()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * const res = ctx.mkTimes(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isDiv()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * const res = ctx.mkDiv(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isPow()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * res = ctx.mkPow(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isAbs()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkAbs(ctx.mkCons(e1));
            return res;
        } else if (e->isSin()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkSin(ctx.mkCons(e1));
            return res;
        } else if (e->isCos()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkCos(ctx.mkCons(e1));
            return res;
        } else if (e->isTan()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkTan(ctx.mkCons(e1));
            return res;
        } else if (e->isAsin()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkAsin(ctx.mkCons(e1));
            return res;
        } else if (e->isAcos()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkAcos(ctx.mkCons(e1));
            return res;
        } else if (e->isAtan()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkAtan(ctx.mkCons(e1));
            return res;
        } else if (e->isLog()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkLog(ctx.mkCons(e1));
            return res;
        } else if (e->isExp()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkExp(ctx.mkCons(e1));
            return res;
        } else if (e->isSqrt()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkSqrt(ctx.mkCons(e1));
            return res;
        } else if (e->isAtan2()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * res = ctx.mkAtan2(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isNot()) {
            assert(e->getArity() == 1);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * res = ctx.mkNot(ctx.mkCons(e1));
            return res;
        } else if (e->isGt()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * res = ctx.mkGt(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isLt()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * res = ctx.mkLt(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isGeq()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * res = ctx.mkGeq(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isLeq()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * res = ctx.mkLeq(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isEq()) {
            assert(e->getArity() == 2);
            Enode * const e1 = subst(ctx, e->get1st(), m);
            Enode * const e2 = subst(ctx, e->get2nd(), m);
            Enode * res = ctx.mkEq(ctx.mkCons(e1, ctx.mkCons(e2)));
            return res;
        } else if (e->isOr()) {
            return ctx.mkOr(subst(ctx, e->getCdr(), m));
        } else if (e->isAnd()) {
            return ctx.mkAnd(subst(ctx, e->getCdr(), m));
        } else {
            ostringstream ss;
            ss << e;
            throw std::runtime_error("Term " + ss.str() + " doesn't have a mapping in enode_subst");
        }
    } else if (e->isList()) {
        if (e->isEnil()) {
            return e;
        } else {
            Enode * new_car = subst(ctx, e->getCar(), m);
            Enode * new_cdr = subst(ctx, e->getCdr(), m);
            return ctx.mkCons(new_car, new_cdr);
        }
    } else if (e->isDef()) {
        cerr << "isDef: " << e << endl;
    } else if (e->isEnil()) {
        cerr << "isEnil: " << e << endl;
    } else {
        opensmt_error("unknown case value");
    }
    return e;
}
}  // namespace dreal
