/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>
        Soonho Kong <soonhok@cs.cmu.edu>

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

#include <list>
#include <string>
#include <vector>
#include "api/dreal.hh"
#include "opensmt/api/OpenSMTContext.h"
#include "util/subst_enode.h"
#include "util/logging.h"

using std::cerr;
using std::endl;
using std::vector;
using std::ostream;
using std::string;
using std::pair;
using std::list;
using std::unordered_map;

namespace dreal {

void check_ctx(expr const & a, expr const & b) {
    (void)(a);
    (void)(b);
    assert(a.get_ctx() == b.get_ctx());
}

expr::expr(solver * const sol, cexpr const e) : m_solver(sol), cctx(sol->get_ctx()), ep(e) {
    assert(m_solver);
    assert(cctx);
    assert(ep);
}

expr::expr(solver& sol, char const * name) : m_solver(&sol), cctx(sol.get_ctx()), ep((sol.var(name)).get_cexpr()) {}

expr::expr(solver * const s, expr * e) : m_solver(s), cctx(s->get_ctx()), ep(e->get_cexpr()) {}

expr::expr(solver * const s) : m_solver(s), cctx(s->get_ctx()) {}

void expr::setContent(solver * s, cexpr c) {
    m_solver = s;
    cctx = s->get_ctx();
    ep = c;
}

string expr::get_name() {
    Enode * e = static_cast<Enode *>(ep);
    return e->getCar()->getName();
}

void expr::set_ub(double const a) {
    Enode * tmp = static_cast<Enode *>(ep);
    tmp->setDomainUpperBound(a);
    tmp->setValueUpperBound(a);
}

void expr::set_lb(double const a) {
    Enode * tmp = static_cast<Enode *>(ep);
    tmp->setDomainLowerBound(a);
    tmp->setValueLowerBound(a);
}

void expr::set_bounds(double const l, double const u) {
    set_lb(l);
    set_ub(u);
}

expr operator==(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkEq(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator==(expr const & e1, double const a) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 == t;
}

expr operator==(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t == e1;
}

expr operator>=(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkGeq(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator>=(expr const & e1, double const a) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 >= t;
}

expr operator>=(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t >= e1;
}

expr operator<=(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkLeq(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator<=(expr const & e1, double const a) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 <= t;
}

expr operator<=(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t <= e1;
}

expr operator<(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkLt(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator<(expr const & e1, double const a) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 < t;
}

expr operator<(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t < e1;
}

expr operator>(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkGt(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator>(expr const & e1, double const a) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 > t;
}

expr operator>(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t > e1;
}

expr operator+(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkPlus(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator+(expr const & e1, double const a) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 + t;
}

expr operator+(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t + e1;
}

expr operator-(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkMinus(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator-(expr const & e1, double const a) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 - t;
}

expr operator-(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t - e1;
}

expr operator-(expr const & e) {
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(e.get_ctx());
    Enode * const args_list = context->mkCons(static_cast<Enode *>(e.get_cexpr()));
    Enode * const res = context->mkUminus(args_list);
    return expr(e.get_solver(), static_cast<cexpr>(res));
}

expr operator*(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkTimes(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator*(expr const & e1, double const a) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 * t;
}

expr operator*(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t * e1;
}

expr operator/(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkDiv(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator/(expr const & e1, double const a) {
    assert(a!= 0);
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return e1 / t;
}

expr operator/(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return t / e1;
}

expr abs(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * const res = context->mkAbs(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr pow(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkPow(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr pow(expr const & e1, double const a) {
    assert(a!= 0);
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return pow(e1, t);
}

expr pow(double const a, expr const & e1) {
    solver * const s = e1.get_solver();
    expr const t = s->num(a);
    return pow(t, e1);
}

expr operator^(expr const & e, double const a) {
    return pow(e, a);
}

expr operator^(double const a, expr const & e) {
    return pow(a, e);
}

expr pow(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkPow(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr sqrt(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkSqrt(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr exp(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkExp(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr log(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkLog(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr sin(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkSin(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr cos(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkCos(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr tan(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkTan(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr asin(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkAsin(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr acos(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkAcos(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr atan(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkAtan(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr sinh(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkSinh(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr cosh(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkCosh(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr tanh(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkTanh(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr operator&&(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkAnd(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator||(expr const & e1, expr const & e2) {
    check_ctx(e1, e2);
    cexpr const ce1 = e1.get_cexpr();
    cexpr const ce2 = e2.get_cexpr();
    list<Enode *> args { static_cast<Enode *>(ce2), static_cast<Enode *>(ce1) };
    env cctx = e1.get_ctx();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const args_list = context->mkCons(args);
    Enode * const res = context->mkOr(args_list);
    return expr(e1.get_solver(), static_cast<cexpr>(res));
}

expr operator!(expr const & arg) {
    env cctx = arg.get_ctx();
    cexpr c_arg = arg.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * args_list = context->mkCons(static_cast<Enode *>(c_arg));
    Enode * res = context->mkNot(static_cast<Enode *>(args_list));
    return expr(arg.get_solver(), static_cast<cexpr>(res));
}

expr implies(expr const & e1, expr const & e2) {
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

expr der(expr const & e, expr const & v) {
    check_ctx(e, v);
    cexpr ce = e.get_cexpr();
    cexpr cv = v.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(e.get_ctx());
    Enode * e_ce = static_cast<Enode *>(ce);
    Enode * e_cv = static_cast<Enode *>(cv);
    Enode * res = context->mkDeriv(e_ce, e_cv);
    return expr(e.get_solver(), static_cast<cexpr>(res));
}

expr upoly(expr const & x, char const * a, unsigned const d) {
    solver * sol = x.get_solver();
    string s(a);
    s += std::to_string(0);
    expr * c_0 = sol->new_var(s.c_str());
    expr result = *c_0;
    for (unsigned i = 1; i < d; ++i) {
        string s(a);
        s += std::to_string(i);
        expr * c_i = sol->new_var(s.c_str());
        result = result + (*c_i) * pow(x, i);
    }
    return result;
}

expr substitute(expr const & e, unordered_map<expr *, expr *> const & m) {
    cexpr ce = e.get_cexpr();
    Enode * e_ce = static_cast<Enode *>(ce);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(e.get_ctx());
    unordered_map<Enode *, Enode *> enode_map;
    for ( auto item : m ) {
        Enode * const e1 = static_cast<Enode*>((item.first)->get_cexpr());
        Enode * const e2 = static_cast<Enode*>((item.second)->get_cexpr());
        if (e1 != e2) {
            enode_map.emplace(e1, e2);
        }
    }
    Enode * res = subst(*context, e_ce, enode_map);
    return expr(e.get_solver(), static_cast<cexpr>(res));
}

expr substitute(expr const & e, vector<expr*> const & pre, vector<expr *> const & post) {
    assert(pre.size() == post.size());
    unordered_map<expr *, expr *> m;
    for (unsigned i=0; i < pre.size(); i++) {
    m.emplace(pre[i], post[i]);
    }
    return substitute(e, m);
}

ostream & operator<<(ostream & out, expr const & e) {
    out << static_cast<Enode *>(e.get_cexpr());
    return out;
}

poly::poly(vector<expr*> & x, char const * c_name, unsigned d) : expr(x[0]->get_solver()), m_x(x) {
    cctx = m_solver->get_ctx();
    degree = d;
    ep = buildExpr(c_name, d);
    m_e = new expr();
    m_e->setContent(m_solver, ep);
}

cexpr poly::buildExpr(char const * c_name, unsigned d) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    // monomials hold all monomials in the polynomial, starting from the constant term
    vector<Enode *> monomials;
    Enode * one = ctx->mkNum("1.0");
    monomials.push_back(one);
    // tmp will hold monomials that are added for each new variable
    vector<Enode *> tmp;
    for (auto xi : m_x) {  // extend existing with new variables
        double power = 0;
        // iterate up to the degree bound
        for (unsigned j = 1; j <= d; j++) {
            power = power + 1;
            for (auto m : monomials) {
                // iterate through every existing monomial m, and push (xi^power)*m as a new monomial
                tmp.push_back(ctx->mkTimes(ctx->mkCons(
                                                ctx->mkPow(ctx->mkCons(static_cast<Enode*>(xi->get_cexpr()),
                                                    ctx->mkCons(ctx->mkNum(power)))), ctx->mkCons(m))));
            }
        }
        // then add the newly constructed monomials to the monomial list
        for (auto tm : tmp) {
              monomials.push_back(tm);
        }
        tmp.clear();
    }
    // ret will hold the full expression
    Enode * ret = ctx->mkNum("0.0");
    unsigned i = 0;
    for (auto m : monomials) {
        // for each monomial, construct a coefficient that will go with it
        string cn(c_name);
        cn += std::to_string(i);
        expr * ci_expr = m_solver->new_var(cn.c_str());
        m_c.push_back(ci_expr);
        // add a new term to ret
        ret = ctx->mkPlus(ctx->mkCons(ret, ctx->mkCons(ctx->mkTimes
                    (ctx->mkCons(m, ctx->mkCons(static_cast<Enode*>(ci_expr->get_cexpr())))))));
        // increment the cofficient count
        i++;
    }
    // put result in the internal cexpr
    return static_cast<cexpr>(ret);
}

poly::~poly() {
    delete m_e;
}

expr * poly::getExpr() {
    return m_e;
}

void poly::setCofBounds(double lb, double ub) {
    for (auto e : m_c) {
        e->set_bounds(lb, ub);
    }
}
}  // namespace dreal
