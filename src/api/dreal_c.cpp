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

#include "api/dreal_c.h"

#include <assert.h>
#include <iostream>
#include <limits>
#include <list>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "./version.h"
#include "common/Global.h"
#include "egraph/Enode.h"
#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Vec.h"
#include "opensmt/api/OpenSMTContext.h"
#include "smtsolvers/SMTConfig.h"
#include "util/logging.h"

class Snode;

using std::string;
using std::numeric_limits;
using std::pair;
using std::cerr;
using std::endl;
using std::ofstream;
using std::ostream;
using std::vector;
using std::pair;
using std::make_pair;
using std::list;
using std::map;
using std::set;

#ifndef SMTCOMP
#define CAST(FROM, TO)                                            \
    assert(FROM);                                                 \
    OpenSMTContext * FROM_ = static_cast<OpenSMTContext *>(FROM); \
    OpenSMTContext & TO = *FROM_;

//
// Communication APIs
//
void dreal_init() {
    static bool already_init = false;
    if (!already_init) {
        const char * argv[] = {};
        START_EASYLOGGINGPP(0, argv);
        already_init = true;
    }
}

void dreal_set_verbosity(dreal_context c, int v) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    if (v > 3) {
        context.setDebug(true);
    } else if (v > 2) {
        context.setVerbose(true);
    }
}

#ifdef USE_CLP
void dreal_use_polytope(dreal_context c) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    c_->getConfig().nra_polytope = true;
}
#endif

void dreal_set_precision(dreal_context c, const double p) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    context.setPrecision(p);
}

double dreal_get_precision(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    return context.getPrecision();
}

char * dreal_version() { return const_cast<char *>(PACKAGE_STRING); }

dreal_context dreal_mk_context(dreal_logic l) {
    OpenSMTContext * c = new OpenSMTContext();
    OpenSMTContext & context = *c;
    // IMPORTANT:
    // Any parameter in the config should be set
    // here, BEFORE SetLogic is called. In SetLogic
    // solvers are initialized with values taken
    // from the config ...
    SMTConfig & config = context.getConfig();
    // When API is active incremental solving must be on
    config.incremental = 1;
    //
    // Set the right logic
    switch (l) {
        case qf_nra:
            context.SetLogic(QF_NRA);
            break;
        case qf_nra_ode:
            context.SetLogic(QF_NRA_ODE);
            break;
            //  dreal_error2("unsupported logic: ", l);
    }

    // Return context
    return static_cast<void *>(c);
}

void dreal_del_context(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    delete c_;
}

void dreal_reset(dreal_context c) {
    CAST(c, context);
    context.Reset();
}

void dreal_print_expr(dreal_expr e) {
    Enode * enode = static_cast<Enode *>(e);
    cerr << enode;
}

void dreal_push(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    context.Push();
}

void dreal_pop(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    context.Pop();
}

void dreal_assert(dreal_context c, dreal_expr e) {
    assert(c);
    assert(e);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * expr = static_cast<Enode *>(e);
    context.Assert(expr);
}

dreal_result dreal_check(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    lbool result = context.CheckSAT();
    if (result == l_Undef) return l_undef;
    if (result == l_False) return l_false;
    return l_true;
}

dreal_result dreal_check_assump(dreal_context c, dreal_expr l) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * unit = static_cast<Enode *>(l);
    assert(unit);
    vec<Enode *> assumptions;
    assumptions.push(unit);
    lbool result = context.CheckSAT(assumptions);
    if (result == l_Undef) return l_undef;
    if (result == l_False) return l_false;
    assert(result == l_True);
    return l_true;
}

dreal_result dreal_check_lim_assump(dreal_context c, dreal_expr l, unsigned limit) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * unit = static_cast<Enode *>(l);
    assert(unit);
    vec<Enode *> assumptions;
    assumptions.push(unit);
    lbool result = context.CheckSAT(assumptions, limit);
    if (result == l_Undef) return l_undef;
    if (result == l_False) return l_false;
    return l_true;
}

//
// Model APIs
//
void dreal_print_model(dreal_context c, const char * filename) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    ofstream os(filename);
    context.PrintModel(os);
}

//
// Formula construction APIs
//

void dreal_define_ode(dreal_context c, const char * flowname, dreal_expr * vars, dreal_expr * rhses,
                      unsigned n) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    vector<pair<Enode *, Enode *>> odes;
    for (unsigned i = 0; i < n; i++) {
        Enode * var = static_cast<Enode *>(vars[i]);
        Enode * rhs = static_cast<Enode *>(rhses[i]);
        odes.push_back(make_pair(var, rhs));
    }
    context.DefineODE(flowname, odes);
}

dreal_expr dreal_mk_integral(dreal_context c, dreal_expr * vars_t, dreal_expr time_l,
                             dreal_expr time_u, dreal_expr * vars_0, unsigned n,
                             const char * flowname) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    list<Enode *> args_t, args_0;
    for (int i = n - 1; i >= 0; --i) {
        Enode * arg_t = static_cast<Enode *>(vars_t[i]);
        Enode * arg_0 = static_cast<Enode *>(vars_0[i]);
        args_t.push_back(arg_t);
        args_0.push_back(arg_0);
    }
    Enode * args_list_t = context.mkCons(args_t);
    Enode * args_list_0 = context.mkCons(args_0);
    Enode * res = context.mkIntegral(static_cast<Enode *>(time_l), static_cast<Enode *>(time_u),
                                     args_list_0, args_list_t, flowname);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_true(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * res = context.mkTrue();
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_false(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * res = context.mkFalse();
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_bool_var(dreal_context c, char const * s) {
    assert(c);
    assert(s);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Snode * sort = context.mkSortBool();
    context.DeclareFun(s, sort);
    Enode * res = context.mkVar(s, true);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_int_var(dreal_context c, char const * s, long lb, long ub) {
    assert(c);
    assert(s);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Snode * sort = context.mkSortInt();
    context.DeclareFun(s, sort);
    Enode * res = context.mkVar(s, true);
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_unbounded_int_var(dreal_context c, char const * s) {
    return dreal_mk_int_var(c, s, numeric_limits<long>::lowest(), numeric_limits<long>::max());
}

dreal_expr dreal_mk_forall_int_var(dreal_context c, char const * s, long lb, long ub) {
    assert(c);
    assert(s);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Snode * sort = context.mkSortInt();
    context.DeclareFun(s, sort);
    Enode * res = context.mkVar(s, true);
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    res->setForallVar();
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_forall_unbounded_int_var(dreal_context c, char const * s) {
    return dreal_mk_int_var(c, s, numeric_limits<long>::lowest(), numeric_limits<long>::max());
}

dreal_expr dreal_mk_real_var(dreal_context c, char const * s, double lb, double ub) {
    assert(c);
    assert(s);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Snode * sort = context.mkSortReal();
    context.DeclareFun(s, sort);
    Enode * res = context.mkVar(s, true);
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_unbounded_real_var(dreal_context c, char const * s) {
    return dreal_mk_real_var(c, s, -numeric_limits<double>::infinity(),
                             numeric_limits<double>::infinity());
}

dreal_expr dreal_mk_forall_real_var(dreal_context c, char const * s, double lb, double ub) {
    assert(c);
    assert(s);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Snode * sort = context.mkSortReal();
    context.DeclareFun(s, sort);
    Enode * res = context.mkVar(s, true);
    res->setDomainLowerBound(lb);
    res->setDomainUpperBound(ub);
    res->setValueLowerBound(lb);
    res->setValueUpperBound(ub);
    res->setForallVar();
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_forall_unbounded_real_var(dreal_context c, char const * s) {
    return dreal_mk_real_var(c, s, numeric_limits<double>::lowest(), numeric_limits<double>::max());
}

dreal_expr dreal_mk_forall(dreal_context c, dreal_expr * varlist, unsigned n, dreal_expr body) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    vector<pair<string, Snode *>> sorted_var_list;
    for (unsigned i = 0; i < n; ++i) {
        dreal_expr var = varlist[i];
        Enode * e = static_cast<Enode *>(var);
        Snode * sort = e->getSort();
        string name = e->getCar()->getNameFull();
        sorted_var_list.push_back(make_pair(name, sort));
    }
    Enode * e_body = static_cast<Enode *>(body);
    Enode * res = context.mkForall(sorted_var_list, e_body);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_or(dreal_context c, dreal_expr * expr_list, unsigned n) {
    assert(c);
    assert(expr_list);
    list<Enode *> args;
    for (unsigned i = 0; i < n; i++) {
        Enode * arg = static_cast<Enode *>(expr_list[i]);
        args.push_back(arg);
    }
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(args);
    Enode * res = context.mkOr(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_or_2(dreal_context c, dreal_expr expr1, dreal_expr expr2) {
    dreal_expr list[2] = {expr1, expr2};
    return dreal_mk_or(c, list, 2);
}

dreal_expr dreal_mk_or_3(dreal_context c, dreal_expr expr1, dreal_expr expr2, dreal_expr expr3) {
    dreal_expr list[3] = {expr1, expr2, expr3};
    return dreal_mk_or(c, list, 3);
}

dreal_expr dreal_mk_and(dreal_context c, dreal_expr * expr_list, unsigned n) {
    assert(c);
    assert(expr_list);
    list<Enode *> args;
    for (unsigned i = 0; i < n; i++) {
        Enode * arg = static_cast<Enode *>(expr_list[i]);
        args.push_back(arg);
    }
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(args);
    Enode * res = context.mkAnd(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_and_2(dreal_context c, dreal_expr expr1, dreal_expr expr2) {
    dreal_expr list[2] = {expr1, expr2};
    return dreal_mk_and(c, list, 2);
}

dreal_expr dreal_mk_and_3(dreal_context c, dreal_expr expr1, dreal_expr expr2, dreal_expr expr3) {
    dreal_expr list[3] = {expr1, expr2, expr3};
    return dreal_mk_and(c, list, 3);
}

dreal_expr dreal_mk_eq(dreal_context c, dreal_expr x, dreal_expr y) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(x), context.mkCons(static_cast<Enode *>(y)));
    Enode * res = context.mkEq(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_ite(dreal_context c, dreal_expr i, dreal_expr t, dreal_expr e) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * i_ = static_cast<Enode *>(i);
    Enode * t_ = static_cast<Enode *>(t);
    Enode * e_ = static_cast<Enode *>(e);
    Enode * args = context.mkCons(i_, context.mkCons(t_, context.mkCons(e_)));
    Enode * res = context.mkIte(args);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_not(dreal_context c, dreal_expr x) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(x));
    Enode * res = context.mkNot(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_num_from_string(dreal_context c, const char * s) {
    assert(c);
    assert(s);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * res = context.mkNum(s);
    return res;
}

dreal_expr dreal_mk_num(dreal_context c, double const v) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * res = context.mkNum(v);
    return res;
}

dreal_expr dreal_mk_plus(dreal_context c, dreal_expr * expr_list, unsigned n) {
    list<Enode *> args;
    for (unsigned i = 0; i < n; i++) {
        Enode * arg = static_cast<Enode *>(expr_list[i]);
        args.push_back(arg);
    }
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(args);
    Enode * res = context.mkPlus(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_plus_2(dreal_context c, dreal_expr expr1, dreal_expr expr2) {
    dreal_expr list[2] = {expr1, expr2};
    return dreal_mk_plus(c, list, 2);
}

dreal_expr dreal_mk_plus_3(dreal_context c, dreal_expr expr1, dreal_expr expr2, dreal_expr expr3) {
    dreal_expr list[3] = {expr1, expr2, expr3};
    return dreal_mk_plus(c, list, 3);
}

dreal_expr dreal_mk_minus(dreal_context c, dreal_expr x, dreal_expr y) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(x), context.mkCons(static_cast<Enode *>(y)));
    Enode * res = context.mkMinus(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_uminus(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkUminus(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_times(dreal_context c, dreal_expr * expr_list, unsigned n) {
    list<Enode *> args;
    for (unsigned i = 0; i < n; i++) {
        Enode * arg = static_cast<Enode *>(expr_list[i]);
        args.push_back(arg);
    }
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(args);
    Enode * res = context.mkTimes(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_times_2(dreal_context c, dreal_expr expr1, dreal_expr expr2) {
    dreal_expr list[2] = {expr1, expr2};
    return dreal_mk_times(c, list, 2);
}

dreal_expr dreal_mk_times_3(dreal_context c, dreal_expr expr1, dreal_expr expr2, dreal_expr expr3) {
    dreal_expr list[3] = {expr1, expr2, expr3};
    return dreal_mk_times(c, list, 3);
}

dreal_expr dreal_mk_div(dreal_context c, dreal_expr x, dreal_expr y) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(x), context.mkCons(static_cast<Enode *>(y)));
    Enode * res = context.mkDiv(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_leq(dreal_context c, dreal_expr lhs, dreal_expr rhs) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(lhs), context.mkCons(static_cast<Enode *>(rhs)));
    Enode * res = context.mkLeq(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_lt(dreal_context c, dreal_expr lhs, dreal_expr rhs) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(lhs), context.mkCons(static_cast<Enode *>(rhs)));
    Enode * res = context.mkLt(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_gt(dreal_context c, dreal_expr lhs, dreal_expr rhs) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(lhs), context.mkCons(static_cast<Enode *>(rhs)));
    Enode * res = context.mkGt(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_geq(dreal_context c, dreal_expr lhs, dreal_expr rhs) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(lhs), context.mkCons(static_cast<Enode *>(rhs)));
    Enode * res = context.mkGeq(args_list);
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_abs(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkAbs(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_exp(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkExp(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_log(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkLog(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_sqrt(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkSqrt(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_pow(dreal_context c, dreal_expr arg1, dreal_expr arg2) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(arg1), context.mkCons(static_cast<Enode *>(arg2)));
    Enode * res = context.mkPow(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_sin(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkSin(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_cos(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkCos(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_tan(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkTan(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_asin(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkAsin(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_acos(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkAcos(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_atan(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkAtan(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_sinh(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkSinh(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_cosh(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkCosh(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_tanh(dreal_context c, dreal_expr arg) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list = context.mkCons(static_cast<Enode *>(arg));
    Enode * res = context.mkTanh(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_atan2(dreal_context c, dreal_expr arg1, dreal_expr arg2) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(arg1), context.mkCons(static_cast<Enode *>(arg2)));
    Enode * res = context.mkAtan2(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_min(dreal_context c, dreal_expr arg1, dreal_expr arg2) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(arg1), context.mkCons(static_cast<Enode *>(arg2)));
    Enode * res = context.mkMin(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}

dreal_expr dreal_mk_max(dreal_context c, dreal_expr arg1, dreal_expr arg2) {
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * args_list =
        context.mkCons(static_cast<Enode *>(arg1), context.mkCons(static_cast<Enode *>(arg2)));
    Enode * res = context.mkMax(static_cast<Enode *>(args_list));
    return static_cast<void *>(res);
}
unsigned dreal_conflicts(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    return context.getLearnts();
}

unsigned dreal_decisions(dreal_context c) {
    assert(c);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    return context.getDecisions();
}

dreal_expr dreal_get_value(dreal_context c, dreal_expr v) {
    assert(c);
    assert(v);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    assert(context.getStatus() == l_True);
    Enode * var = static_cast<Enode *>(v);
    const Real & value = var->getValue();
    Enode * res = context.mkNum(value);
    return static_cast<void *>(res);
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
double dreal_get_lb(dreal_context c, dreal_expr v) {
    assert(c);
    assert(v);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    assert(context.getStatus() == l_True);
    Enode * var = static_cast<Enode *>(v);
    return var->getValueLowerBound();
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
double dreal_get_ub(dreal_context c, dreal_expr v) {
    assert(c);
    assert(v);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    assert(context.getStatus() == l_True);
    Enode * var = static_cast<Enode *>(v);
    return var->getValueUpperBound();
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
double dreal_get_domain_lb(dreal_context c, dreal_expr v) {
    assert(c);
    assert(v);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    assert(context.getStatus() == l_True);
    Enode * var = static_cast<Enode *>(v);
    return var->getDomainLowerBound();
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
double dreal_get_domain_ub(dreal_context c, dreal_expr v) {
    assert(c);
    assert(v);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    assert(context.getStatus() == l_True);
    Enode * var = static_cast<Enode *>(v);
    return var->getDomainUpperBound();
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
void dreal_set_domain_lb(dreal_context c, dreal_expr v, double n) {
    assert(c);
    assert(v);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    assert(context.getStatus() == l_True);
    Enode * var = static_cast<Enode *>(v);
    var->setDomainLowerBound(n);
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
void dreal_set_domain_ub(dreal_context c, dreal_expr v, double n) {
    assert(c);
    assert(v);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    assert(context.getStatus() == l_True);
    Enode * var = static_cast<Enode *>(v);
    var->setDomainUpperBound(n);
}
#pragma GCC diagnostic pop

dreal_result dreal_get_bool(dreal_context c, dreal_expr p) {
    assert(c);
    assert(p);
    OpenSMTContext * c_ = static_cast<OpenSMTContext *>(c);
    OpenSMTContext & context = *c_;
    Enode * atom = static_cast<Enode *>(p);
    lbool value = context.getModel(atom);
    if (value == l_True) {
        return l_true;
    } else if (value == l_False) {
        return l_false;
    }
    return l_undef;
}
#endif
