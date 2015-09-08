/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
        Soonho  Kong        <soonhok@cs.cmu.edu>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso
dReal   -- Copyright (C) 2013 -- 2015, Soonho Kong

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef OPENSMT_C_H
#define OPENSMT_C_H

#ifdef __cplusplus
extern "C" {
#endif

//
// Datatypes
//
typedef void * opensmt_expr;
typedef void * opensmt_context;
typedef enum { l_false=-1, l_undef, l_true } opensmt_result;
typedef enum
{
  qf_nra,        // Non-Linear Real Arithmetic
  qf_nra_ode    // Non-Linear Real Arithmetic
} opensmt_logic;

//
// Communication APIs
//
void             opensmt_init                      ();
void             opensmt_set_verbosity             ( opensmt_context, int );
void             opensmt_set_precision             ( opensmt_context c, const double p);
double           opensmt_get_precision             ( opensmt_context c );
char *           opensmt_version                   ( );
void             opensmt_print_expr                ( opensmt_expr );
opensmt_context  opensmt_mk_context                ( opensmt_logic );
void             opensmt_del_context               ( opensmt_context );
void             opensmt_reset                     ( opensmt_context );
void             opensmt_push                      ( opensmt_context );
void             opensmt_pop                       ( opensmt_context );
void             opensmt_assert                    ( opensmt_context, opensmt_expr );
opensmt_result   opensmt_check                     ( opensmt_context );
opensmt_result   opensmt_check_assump              ( opensmt_context, opensmt_expr );
opensmt_result   opensmt_check_lim_assump          ( opensmt_context, opensmt_expr, unsigned );
unsigned         opensmt_conflicts                 ( opensmt_context );
unsigned         opensmt_decisions                 ( opensmt_context );
opensmt_expr     opensmt_get_value                 ( opensmt_context, opensmt_expr );
double           opensmt_get_lb                    ( opensmt_context, opensmt_expr );
double           opensmt_get_ub                    ( opensmt_context, opensmt_expr );
double           opensmt_get_bound_lb              ( opensmt_context, opensmt_expr );
double           opensmt_get_bound_ub              ( opensmt_context, opensmt_expr );
void             opensmt_set_bound_lb              ( opensmt_context, opensmt_expr, double );
void             opensmt_set_bound_ub              ( opensmt_context, opensmt_expr, double );
double           opensmt_get_domain_lb             ( opensmt_context, opensmt_expr );
double           opensmt_get_domain_ub             ( opensmt_context, opensmt_expr );
void             opensmt_set_domain_lb             ( opensmt_context, opensmt_expr, double );
void             opensmt_set_domain_ub             ( opensmt_context, opensmt_expr, double );
opensmt_result   opensmt_get_bool                  ( opensmt_context c, opensmt_expr p );
void             opensmt_prefer                    ( opensmt_expr a );
void             opensmt_polarity                  ( opensmt_context c, opensmt_expr a, int pos );


void             opensmt_print_model               ( opensmt_context, const char * );
void             opensmt_print_proof               ( opensmt_context, const char * );
void             opensmt_print_interpolant         ( opensmt_context, const char * );

void             opensmt_define_ode                ( opensmt_context, const char *, opensmt_expr *, opensmt_expr *, unsigned);
opensmt_expr     opensmt_mk_integral               ( opensmt_context, opensmt_expr *, opensmt_expr, opensmt_expr, opensmt_expr *, unsigned, const char *);

opensmt_expr     opensmt_mk_true                   ( opensmt_context );
opensmt_expr     opensmt_mk_false                  ( opensmt_context );
opensmt_expr     opensmt_mk_bool_var               ( opensmt_context, char const * );
opensmt_expr     opensmt_mk_int_var                ( opensmt_context, char const * , long , long );
opensmt_expr     opensmt_mk_unbounded_int_var      ( opensmt_context, char const * );
opensmt_expr     opensmt_mk_forall_int_var         ( opensmt_context, char const * , long , long );
opensmt_expr     opensmt_mk_forall_unbounded_int_var ( opensmt_context, char const * , long , long );
opensmt_expr     opensmt_mk_real_var               ( opensmt_context, char const * , double, double );
opensmt_expr     opensmt_mk_unbounded_real_var     ( opensmt_context, char const * );
opensmt_expr     opensmt_mk_forall_real_var        ( opensmt_context, char const * , double, double );
opensmt_expr     opensmt_mk_forall_unbounded_real_var ( opensmt_context, char const * );
opensmt_expr     opensmt_mk_forall                 ( opensmt_context, opensmt_expr *, unsigned, opensmt_expr );
opensmt_expr     opensmt_mk_or                     ( opensmt_context, opensmt_expr *, unsigned );
opensmt_expr     opensmt_mk_or_2                   ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_or_3                   ( opensmt_context, opensmt_expr, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_and                    ( opensmt_context, opensmt_expr *, unsigned );
opensmt_expr     opensmt_mk_and_2                  ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_and_3                  ( opensmt_context, opensmt_expr, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_eq                     ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_ite                    ( opensmt_context, opensmt_expr, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_not                    ( opensmt_context, opensmt_expr );
opensmt_expr     opensmt_mk_num_from_string        ( opensmt_context, const char * );
opensmt_expr     opensmt_mk_num                    ( opensmt_context, double const );
opensmt_expr     opensmt_mk_plus                   ( opensmt_context, opensmt_expr *, unsigned );
opensmt_expr     opensmt_mk_plus_2                 ( opensmt_context, opensmt_expr, opensmt_expr);
opensmt_expr     opensmt_mk_plus_3                 ( opensmt_context, opensmt_expr, opensmt_expr, opensmt_expr);
opensmt_expr     opensmt_mk_minus                  ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_uminus                 ( opensmt_context, opensmt_expr );
opensmt_expr     opensmt_mk_times                  ( opensmt_context, opensmt_expr *, unsigned );
opensmt_expr     opensmt_mk_times_2                ( opensmt_context, opensmt_expr, opensmt_expr);
opensmt_expr     opensmt_mk_times_3                ( opensmt_context, opensmt_expr, opensmt_expr, opensmt_expr);
opensmt_expr     opensmt_mk_div                    ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_lt                     ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_leq                    ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_gt                     ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_geq                    ( opensmt_context, opensmt_expr, opensmt_expr );

opensmt_expr     opensmt_mk_abs                    ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_exp                    ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_log                    ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_sqrt                   ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_pow                    ( opensmt_context, opensmt_expr, opensmt_expr);
opensmt_expr     opensmt_mk_sin                    ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_cos                    ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_tan                    ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_asin                   ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_acos                   ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_atan                   ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_sinh                   ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_cosh                   ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_tanh                   ( opensmt_context, opensmt_expr);
opensmt_expr     opensmt_mk_atan2                  ( opensmt_context, opensmt_expr, opensmt_expr);
opensmt_expr     opensmt_mk_min                    ( opensmt_context, opensmt_expr, opensmt_expr);
opensmt_expr     opensmt_mk_max                    ( opensmt_context, opensmt_expr, opensmt_expr);
#ifdef __cplusplus
}
#endif

#endif
