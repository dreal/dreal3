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

#include <limits>
#include <string>
#include "dreal.hh"
#include "opensmt/api/OpenSMTContext.h"

using std::cerr;
using std::endl;
using std::vector;
using std::ostream;
using std::string;
using std::numeric_limits;
using std::list;

namespace dreal {
solver::solver() {
    OpenSMTContext * ctx = new OpenSMTContext();
    SMTConfig & config = ctx->getConfig();
    config.incremental = 1;
    ctx->SetLogic(QF_NRA);
    cctx = static_cast<env>(ctx);
}

solver::~solver() {
    assert(cctx);
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    delete ctx;
}

expr solver::var(char const * s , double lb, double ub) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Snode * sort = ctx->mkSortReal();
    ctx->DeclareFun(s, sort);
    Enode * res = ctx->mkVar(s, true);
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    return expr(this, static_cast<cexpr>(res));
}

expr solver::var(char const * s , int lb, int ub) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Snode * sort = ctx->mkSortInt();
    ctx->DeclareFun(s, sort);
    Enode * res = ctx->mkVar(s, true);
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    return expr(this, static_cast<cexpr>(res));
}

expr solver::var(char const * s, vtype t) {
    if (t == vtype::Int) {
        return var(s, numeric_limits<int>::lowest(), numeric_limits<int>::max());
    } else if (t == vtype::Real) {
        return var(s, -numeric_limits<double>::infinity(), numeric_limits<double>::infinity());
    } else {
        OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
        Snode * sort = ctx->mkSortBool();
        ctx->DeclareFun(s, sort);
        Enode * res = ctx->mkVar(s, true);
        return expr(this, static_cast<cexpr>(res));
    }
}

expr solver::var(char const * s) {
    return var(s, vtype::Real);
}

expr solver::num(char const * const s) {
    assert(s);
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Enode * res = ctx->mkNum(s);
    return expr(this, static_cast<cexpr>(res));
}

expr solver::num(double const v) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Enode * res = ctx->mkNum(v);
    return expr(this, static_cast<cexpr>(res));
}


expr solver::num(int const v) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Enode * res = ctx->mkNum(v);
    return expr(this, static_cast<cexpr>(res));
}

void solver::reset() {
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    context->Reset();
}

void solver::push() {
    assert(cctx);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    context->Push();
}

void solver::pop() {
    assert(cctx);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    context->Pop();
}

void solver::add(expr const & e) {
    assert(cctx);
    cexpr l = e.get_cexpr();
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    Enode * const enode = static_cast<Enode *>(l);
    context->Assert(enode);
}

bool solver::check() {
    assert(cctx);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    lbool result = context->CheckSAT();
    assert(result != l_Undef);
    if (result == l_True)
        return true;
    else
        return false;
}

result solver::check_assump(expr const & e) {
    assert(cctx);
    cexpr l = e.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * unit = static_cast<Enode *>(l);
    assert(unit);
    vec<Enode *> assumptions;
    assumptions.push(unit);
    lbool res = context->CheckSAT(assumptions);
    if (res == l_Undef) return result::Undef;
    if (res == l_False) return result::False;
    assert(res == l_True);
    return result::True;
}

result solver::check_lim_assump(expr const & e, unsigned const limit) {
    assert(cctx);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    cexpr l = e.get_cexpr();
    Enode * unit = static_cast<Enode *>(l);
    assert(unit);
    vec<Enode *> assumptions;
    assumptions.push(unit);
    lbool res = context->CheckSAT(assumptions, limit);
    if (res == l_Undef) return result::Undef;
    if (res == l_False) return result::False;
    assert(res == l_True);
    return result::True;
}

expr solver::get_value(expr const & e) {
    cexpr v = e.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    assert(context->getStatus() == l_True);
    Enode * var = static_cast<Enode *>(v);
    const double & value = var->getValue();
    Enode * res = context->mkNum(value);
    return expr(this, static_cast<void *>(res));
}

double solver::get_lb(expr const & e) const {
    cexpr v = e.get_cexpr();
#ifndef NDEBUG
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    assert(context->getStatus() == l_True);
#endif
    Enode * var = static_cast<Enode *>(v);
    return var->getValueLowerBound();
}

double solver::get_ub(expr const & e) const {
    cexpr v = e.get_cexpr();
#ifndef NDEBUG
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    assert(context->getStatus() == l_True);
#endif
    Enode * var = static_cast<Enode *>(v);
    return var->getValueUpperBound();
}

double solver::get_domain_lb(expr const & e) const {
    cexpr v = e.get_cexpr();
#ifndef NDEBUG
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    assert(context->getStatus() == l_True);
#endif
    Enode * var = static_cast<Enode *>(v);
    return var->getDomainLowerBound();
}

double solver::get_domain_ub(expr const & e) const {
    cexpr v = e.get_cexpr();
#ifndef NDEBUG
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    assert(context->getStatus() == l_True);
#endif
    Enode * var = static_cast<Enode *>(v);
    return var->getDomainUpperBound();
}

void solver::set_domain_lb(expr & e, double const n) {
    cexpr v = e.get_cexpr();
#ifndef NDEBUG
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    assert(context->getStatus() == l_True);
#endif
    Enode * var = static_cast<Enode *>(v);
    var->setDomainLowerBound(n);
}

void solver::set_domain_ub(expr & e, double const n) {
    cexpr v = e.get_cexpr();
#ifndef NDEBUG
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    assert(context->getStatus() == l_True);
#endif
    Enode * var = static_cast<Enode *>(v);
    var->setDomainUpperBound(n);
}
}  // namespace dreal
