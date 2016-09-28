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

#pragma once
#include "./dreal_config.h"

#ifdef __cplusplus
extern "C" {
#endif
typedef void * dreal_expr;
typedef void * dreal_context;
typedef enum { l_false = -1, l_undef, l_true } dreal_result;
typedef enum { qf_nra, qf_nra_ode } dreal_logic;
void dreal_init();
void dreal_set_verbosity(dreal_context, int);
void dreal_set_precision(dreal_context c, const double p);
double dreal_get_precision(dreal_context c);
#ifdef USE_CLP
void dreal_use_polytope(dreal_context);
#endif
char * dreal_version();
void dreal_print_expr(dreal_expr);
dreal_context dreal_mk_context(dreal_logic);
void dreal_del_context(dreal_context);
void dreal_reset(dreal_context);
void dreal_push(dreal_context);
void dreal_pop(dreal_context);
void dreal_assert(dreal_context, dreal_expr);
dreal_result dreal_check(dreal_context);
dreal_result dreal_check_assump(dreal_context, dreal_expr);
dreal_result dreal_check_lim_assump(dreal_context, dreal_expr, unsigned);
unsigned dreal_conflicts(dreal_context);
unsigned dreal_decisions(dreal_context);
dreal_expr dreal_get_value(dreal_context, dreal_expr);
double dreal_get_lb(dreal_context, dreal_expr);
double dreal_get_ub(dreal_context, dreal_expr);
double dreal_get_domain_lb(dreal_context, dreal_expr);
double dreal_get_domain_ub(dreal_context, dreal_expr);
void dreal_set_domain_lb(dreal_context, dreal_expr, double);
void dreal_set_domain_ub(dreal_context, dreal_expr, double);
dreal_result dreal_get_bool(dreal_context c, dreal_expr p);
void dreal_print_model(dreal_context, const char *);
void dreal_define_ode(dreal_context, const char *, dreal_expr *, dreal_expr *, unsigned);
dreal_expr dreal_mk_integral(dreal_context, dreal_expr *, dreal_expr, dreal_expr, dreal_expr *,
                             unsigned, const char *);
dreal_expr dreal_mk_true(dreal_context);
dreal_expr dreal_mk_false(dreal_context);
dreal_expr dreal_mk_bool_var(dreal_context, char const *);
dreal_expr dreal_mk_int_var(dreal_context, char const *, long, long);
dreal_expr dreal_mk_unbounded_int_var(dreal_context, char const *);
dreal_expr dreal_mk_forall_int_var(dreal_context, char const *, long, long);
dreal_expr dreal_mk_forall_unbounded_int_var(dreal_context, char const *);
dreal_expr dreal_mk_real_var(dreal_context, char const *, double, double);
dreal_expr dreal_mk_unbounded_real_var(dreal_context, char const *);
dreal_expr dreal_mk_forall_real_var(dreal_context, char const *, double, double);
dreal_expr dreal_mk_forall_unbounded_real_var(dreal_context, char const *);
dreal_expr dreal_mk_forall(dreal_context, dreal_expr *, unsigned, dreal_expr);
dreal_expr dreal_mk_or(dreal_context, dreal_expr *, unsigned);
dreal_expr dreal_mk_or_2(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_or_3(dreal_context, dreal_expr, dreal_expr, dreal_expr);
dreal_expr dreal_mk_and(dreal_context, dreal_expr *, unsigned);
dreal_expr dreal_mk_and_2(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_and_3(dreal_context, dreal_expr, dreal_expr, dreal_expr);
dreal_expr dreal_mk_eq(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_ite(dreal_context, dreal_expr, dreal_expr, dreal_expr);
dreal_expr dreal_mk_not(dreal_context, dreal_expr);
dreal_expr dreal_mk_num_from_string(dreal_context, const char *);
dreal_expr dreal_mk_num(dreal_context, double const);
dreal_expr dreal_mk_plus(dreal_context, dreal_expr *, unsigned);
dreal_expr dreal_mk_plus_2(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_plus_3(dreal_context, dreal_expr, dreal_expr, dreal_expr);
dreal_expr dreal_mk_minus(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_uminus(dreal_context, dreal_expr);
dreal_expr dreal_mk_times(dreal_context, dreal_expr *, unsigned);
dreal_expr dreal_mk_times_2(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_times_3(dreal_context, dreal_expr, dreal_expr, dreal_expr);
dreal_expr dreal_mk_div(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_lt(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_leq(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_gt(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_geq(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_abs(dreal_context, dreal_expr);
dreal_expr dreal_mk_exp(dreal_context, dreal_expr);
dreal_expr dreal_mk_log(dreal_context, dreal_expr);
dreal_expr dreal_mk_sqrt(dreal_context, dreal_expr);
dreal_expr dreal_mk_pow(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_sin(dreal_context, dreal_expr);
dreal_expr dreal_mk_cos(dreal_context, dreal_expr);
dreal_expr dreal_mk_tan(dreal_context, dreal_expr);
dreal_expr dreal_mk_asin(dreal_context, dreal_expr);
dreal_expr dreal_mk_acos(dreal_context, dreal_expr);
dreal_expr dreal_mk_atan(dreal_context, dreal_expr);
dreal_expr dreal_mk_sinh(dreal_context, dreal_expr);
dreal_expr dreal_mk_cosh(dreal_context, dreal_expr);
dreal_expr dreal_mk_tanh(dreal_context, dreal_expr);
dreal_expr dreal_mk_atan2(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_min(dreal_context, dreal_expr, dreal_expr);
dreal_expr dreal_mk_max(dreal_context, dreal_expr, dreal_expr);

// void dreal_polarity(dreal_context c, dreal_expr a, int pos);
// void dreal_prefer(dreal_expr a);
// void dreal_print_proof(dreal_context, const char *);
// void dreal_print_interpolant(dreal_context, const char *);
#ifdef __cplusplus
}
#endif
