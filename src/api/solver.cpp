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

#include <limits>
#include <string>
#include "api/dreal.hh"
#include "opensmt/api/OpenSMTContext.h"

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
    for (auto v : vtab) delete v;
    for (auto n : ntab) delete n;
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    delete ctx;
}

expr * solver::new_var(char const * s, double const lb, double const ub) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Snode * sort = ctx->mkSortReal();
    ctx->DeclareFun(s, sort);
    Enode * res = ctx->mkVar(s, true);
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    expr * v = new expr(this, static_cast<cexpr>(res));
    vtab.push_back(v);
    return v;
}

expr solver::var(char const * s, double const lb, double const ub) {
    return *new_var(s, lb, ub);
}

expr * solver::new_ivar(char const * s, int const lb, int const ub) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Snode * sort = ctx->mkSortInt();
    ctx->DeclareFun(s, sort);
    Enode * res = ctx->mkVar(s, true);
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    expr * v = new expr(this, static_cast<cexpr>(res));
    vtab.push_back(v);
    return v;
}

expr solver::ivar(char const * s, int const lb, int const ub) {
    return *new_ivar(s, lb, ub);
}

expr solver::var(char const * s, vtype const t) {
    if (t == vtype::Int) {
        return ivar(s, numeric_limits<int>::lowest(), numeric_limits<int>::max());
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

expr * solver::new_var(char const * s, vtype const t) {
    assert(t != vtype::Boolean);
    if (t == vtype::Int) {
        return new_ivar(s, numeric_limits<int>::lowest(), numeric_limits<int>::max());
    } else {
        return new_var(s, -numeric_limits<double>::infinity(), numeric_limits<double>::infinity());
    }
}

expr solver::var(char const * s) {
    return var(s, vtype::Real);
}

expr * solver::new_var(char const * s) {
    return new_var(s, vtype::Real);
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

expr * solver::new_num(double const v) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Enode * c = ctx->mkNum(v);
    expr * res = new expr(this, static_cast<cexpr>(c));
    ntab.push_back(res);
    return res;
}

expr solver::num(int const v) {
    OpenSMTContext * ctx = static_cast<OpenSMTContext *>(cctx);
    Enode * res = ctx->mkNum(v);
    return expr(this, static_cast<cexpr>(res));
}

void solver::reset() {
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    vtab.clear();
    stab.clear();
    etab.clear();
    context->Reset();
}

void solver::push() {
    assert(cctx);
    // TODO(sean): take care of etab
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
    etab.push_back(&e);
    context->Assert(enode);
}

bool solver::check() {
    assert(cctx);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    lbool result = context->CheckSAT();
    assert(result != l_Undef);
    stab.clear();
    if (result == l_True) {
        for (auto v : vtab) {
            stab.push_back((get_lb(*v) + get_ub(*v))/2);
        }
        return true;
    } else {
        return false;
    }
}

Bool solver::check_assump(expr const & e) {
    assert(cctx);
    cexpr l = e.get_cexpr();
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    Enode * unit = static_cast<Enode *>(l);
    assert(unit);
    vec<Enode *> assumptions;
    assumptions.push(unit);
    lbool res = context->CheckSAT(assumptions);
    if (res == l_Undef) return Bool::Undef;
    if (res == l_False) return Bool::False;
    assert(res == l_True);
    return Bool::True;
}

Bool solver::check_lim_assump(expr const & e, unsigned const limit) {
    assert(cctx);
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    cexpr l = e.get_cexpr();
    Enode * unit = static_cast<Enode *>(l);
    assert(unit);
    vec<Enode *> assumptions;
    assumptions.push(unit);
    lbool res = context->CheckSAT(assumptions, limit);
    if (res == l_Undef) return Bool::Undef;
    if (res == l_False) return Bool::False;
    assert(res == l_True);
    return Bool::True;
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

double solver::get_value(expr const & e) const {
    return (get_lb(e)+get_ub(e))/2;
}

void solver::print_model(std::ostream & out) {
    OpenSMTContext * context = static_cast<OpenSMTContext *>(cctx);
    if (context->getStatus() == l_True) {
        out << "The input formula is delta-satisfied by the following model: "<< endl;
        for (auto const v : vtab) {
            out << "\t" << *v << " = " << (get_lb(*v) + get_ub(*v))/2 << endl;
        }
    } else {
        out << "No model satisfies the formula." << endl;
    }
}

void solver::print_problem(std::ostream & out) {
    out << "The problem has the following variables:" << endl;
    for (auto const v : vtab) {
        Enode * ev = static_cast<Enode *>(v->get_cexpr());
        out << "\t" << *v  << ": [" << ev->getDomainLowerBound() << ","
            << ev->getDomainUpperBound() <<"]" << endl;
    }
    out << "and the following constraints:" << endl;
    for (auto const e : etab) {
        out << "\t" << *e << endl;
    }
}

void solver::set_verbose(bool const b) {
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    context->getConfig().setVerbosityInfoLevel();
    context->getConfig().nra_verbose = b;
}

void solver::set_delta(double const d) {
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    context->setPrecision(d);
}

void solver::set_polytope(bool const b) {
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    context->getConfig().nra_polytope = b;
}

#ifdef USE_GLPK
void solver::set_lp(bool const b) {
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    context->getConfig().nra_lp = b;
}

void solver::set_lp_only(bool const b) {
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    context->getConfig().nra_linear_only = b;
}
#endif

void solver::set_simulation(bool const b) {
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    context->getConfig().nra_simulation_thread = b;
}

bool solver::solve() {
    bool res = check();
    print_model();
    return res;
}

ostream & solver::dump_formulas(ostream & out) const {
    OpenSMTContext * const context = static_cast<OpenSMTContext *>(cctx);
    return context->dumpFormulas(out);
}
}  // namespace dreal
