/*********************************************************************
Author: Soonho Kong

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

#include "util/enode_utils.h"

#include <assert.h>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "api/OpenSMTContext.h"
#include "common/Global.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/egraph/Enode.h"

class Snode;

using std::cerr;
using std::cout;
using std::endl;
using std::ostringstream;
using std::pair;
using std::runtime_error;
using std::string;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {

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
            return e;
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

/// strengthening a constraint (Enode) by eps (positive constant)
Enode * strengthen_enode(Egraph & eg, Enode * const e, double const eps, bool const polarity) {
    if (e->isNot()) {
        return strengthen_enode(eg, e->get1st(), eps, !polarity);
    }
    if (polarity && e->isEq()) {
        // e1 == e2  ==>  (a == 0)   (no change)
        return e;
    }
    Enode * const e1 = e->get1st();
    Enode * const e2 = e->get2nd();
    if (!polarity && e->isEq()) {
        // Note: |e1 - e2| >= eps encoding is not working well. It
        // doesn't provide enough pruning power.
        // We're using (e1 - e2)^2 >= eps^2 encoding.
        Enode * const eps_node_sq = eg.mkNum(eps * eps);
        return eg.mkGeq(eg.cons(eg.mkPow(eg.cons(eg.mkMinus(e1, e2), eg.cons(eg.mkNum(2.0)))),
                                eg.cons(eps_node_sq)));
    }
    Enode * const eps_node = eg.mkNum(eps);
    if ((polarity && e->isLt()) || (!polarity && e->isGeq())) {
        // e1 <  e2  ==>  e1 < e2 - eps
        return eg.mkLt(eg.cons(e1, eg.cons(eg.mkMinus(e2, eps_node))));
    }
    if ((polarity && e->isLeq()) || (!polarity && e->isGt())) {
        // e1 <= e2  ==>  e1 <= e2 - eps
        return eg.mkLeq(eg.cons(e1, eg.cons(eg.mkMinus(e2, eps_node))));
    }
    if ((polarity && e->isGt()) || (!polarity && e->isLeq())) {
        // e1 >  e2  ==>  e1 > e2 + eps
        return eg.mkGt(eg.cons(e1, eg.cons(eg.mkPlus(e2, eps_node))));
    }
    if ((polarity && e->isGeq()) || (!polarity && e->isLt())) {
        // e1 >= e2  ==>  e1 >= e2 + eps
        return eg.mkGeq(eg.cons(e1, eg.cons(eg.mkPlus(e2, eps_node))));
    }
    // Something is wrong.
    ostringstream os;
    os << "strengthen_enode: should be unreachable (Enode = " << e << ")";
    throw runtime_error(os.str());
}

Enode * wrap_enode_including_forall_vars(OpenSMTContext * ctx, Enode * const e) {
    // Case 1)
    //    !e  -->  ! wrap_enode_including_forall_vars(e)
    if (e->isNot()) {
        return ctx->mkNot(ctx->mkCons(wrap_enode_including_forall_vars(ctx, e->get1st())));
    }
    // Case 2)
    //    e_1 /\ ... /\ e_n
    // -> wrap_enode_including_forall_vars(e_1) /\ ... /\ wrap_enode_including_forall_vars(e_n)
    if (e->isAnd()) {
        Enode * list = e->getCdr();
        Enode * args = nullptr;
        while (!list->isEnil()) {
            Enode * const item = list->getCar();
            Enode * const processed_item = wrap_enode_including_forall_vars(ctx, item);
            if (!args) {
                args = ctx->mkCons(processed_item);
            } else {
                args = ctx->mkCons(processed_item, args);
            }
            list = list->getCdr();
        }
        return ctx->mkAnd(args);
    }
    // Case 3)
    //    e -> (forall ((v_1 Real) ... (v_m Real)) e)
    // where forall_vars(e) = {v_1, ..., v_m}
    vector<pair<string, Snode *>> sorted_var_list;
    unordered_set<Enode *> const forall_vars = e->get_forall_vars();
    if (!forall_vars.empty()) {
        for (Enode * const forall_var : forall_vars) {
            string const name = forall_var->getCar()->getName();
            Snode * const sort = forall_var->getSort();
            sorted_var_list.emplace_back(name, sort);
        }
        return ctx->mkForall(sorted_var_list, e);
    } else {
        return e;
    }
}
}  // namespace dreal
