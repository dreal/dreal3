/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>
        Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2016, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <list>
#include "dreal.hh"
#include "opensmt/api/OpenSMTContext.h"

using std::cerr;
using std::endl;
using std::vector;
using std::ostream;
using std::string;
using std::pair;
using std::list;

namespace dreal {

void check_ctx(expr & a, expr & b) { assert(a.get_ctx() == b.get_ctx()); }

expr::expr(solver * sol, cexpr e) : s(sol), cctx(sol->get_ctx()), ep(e) {
    assert(s);
    assert(cctx);
    assert(ep);
}

expr operator==(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(e1.get_cexpr());
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(e1.get_ctx());
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkEq(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator==(expr e1, double a) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 == t;
}


expr operator==(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t == e1;
}

expr operator>=(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(e1.get_cexpr());
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(e1.get_ctx());
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkGeq(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}


expr operator>=(expr e1, double a) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 >= t;
}


expr operator>=(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t >= e1;
}


expr operator<=(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(e1.get_cexpr());
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(e1.get_ctx());
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkLeq(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}


expr operator<=(expr e1, double a) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 <= t;
}

expr operator<=(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t <= e1;
}



expr operator<(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(e1.get_cexpr());
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(e1.get_ctx());
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkLt(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator<(expr e1, double a) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 < t;
}

expr operator<(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t < e1;
}

expr operator>(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(e1.get_cexpr());
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(e1.get_ctx());
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkGt(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator>(expr e1, double a) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 < t;
}

expr operator>(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t < e1;
}


expr operator+(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce1 = e1.get_cexpr();
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(ce1);
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkPlus(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator+(expr e1, double a) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 + t;
}

expr operator+(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t + e1;
}


expr operator-(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce1 = e1.get_cexpr();
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(ce1);
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkMinus(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator-(expr e1, double a) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 - t;
}

expr operator-(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t - e1;
}

expr operator-(expr e) {
    OpenSMTContext * context = static_cast<OpenSMTContext *>(e.get_ctx());
    Enode * args_list = context->mkCons(static_cast<Enode *>(e.get_cexpr()));
    Enode * res = context->mkUminus(args_list);
    return expr(e.get_solver(), static_cast<cexpr>(res));
}


expr operator*(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce1 = e1.get_cexpr();
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(ce1);
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkTimes(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator*(expr e1, double a) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 * t;
}

expr operator*(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t * e1;
}

expr operator/(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce1 = e1.get_cexpr();
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(ce1);
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkDiv(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator/(expr e1, double a) {
    assert(a!= 0);
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return e1 / t;
}

expr operator/(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return t / e1;
}

expr abs(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkAbs(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr pow(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce1 = e1.get_cexpr();
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(ce1);
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkPow(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr pow(expr e1, double a) {
    assert(a!= 0);
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return pow(e1, t);
}

expr pow(double a, expr e1) {
    solver* s = e1.get_solver();
    expr t = s->num(a);
    return pow(t, e1);
}

expr operator^(expr e1, expr e2) {
    return pow(e1, e2);
}

expr operator^(expr e, double a) {
    return pow(e, a);
}

expr operator^(double a, expr e) {
    return pow(a, e);
}

expr pow(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkPow(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr sqrt(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkSqrt(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr log(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkLog(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr sin(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkSin(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr cos(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkCos(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr tan(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkTan(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr asin(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkAsin(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr acos(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkAcos(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr atan(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkAtan(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr sinh(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkSinh(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr cosh(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkCosh(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr tanh(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkTanh(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr operator&&(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce1 = e1.get_cexpr();
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(ce1);
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkAnd(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator||(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce1 = e1.get_cexpr();
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(ce1);
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkOr(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator!(expr arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkNot(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr implies(expr e1, expr e2) {
    check_ctx(e1, e2);
    cexpr ce1 = e1.get_cexpr();
    cexpr ce2 = e2.get_cexpr();
    list<Enode *> args;
    Enode * arg = static_cast<Enode *>(ce1);
    args.push_back(arg);
    arg = static_cast<Enode *>(ce2);
    args.push_back(arg);
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(args);
    Enode * res = context->mkImplies(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

ostream & operator<<(ostream & out, expr const & e) {
    out << static_cast<Enode *>(e.get_cexpr());
    return out;
}

/*
expr Not (expr);
expr And (expr *, unsigned);
expr And (expr, expr);
expr And (expr, expr, expr);
expr Or	(expr *, unsigned);
expr Or (expr, expr);
expr Or (expr, expr, expr);
expr Ite (expr, expr, expr);
*/

}  // namespace dreal
