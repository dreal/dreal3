#pragma once

#include <iostream>
#include <vector>
#include <utility>
#include <string>
#include <list>

namespace dreal {

typedef enum { dr_false=-1, dr_undef, dr_true } result;
typedef enum { qf_nra, qf_nra_ode } logic;

typedef void * expr;
typedef void * env;

class drealsolver {

public:
    drealsolver();
    ~drealsolver();

    //boolean constants
    expr    mk_true	();
    expr    mk_false	();

    //variables
    expr    mk_bool_var ( char const * );
    expr    mk_int_var	( char const *, long, long );
    expr    mk_int_var  ( char const * );
    expr    mk_real_var ( char const * , double, double );
    expr    mk_real_var	( char const * );
    expr    mk_forall_real_var	( char const * , double, double );
    expr    mk_forall_real_var	( char const * );

    //numerical constants
    expr    mk_num ( double const );
    expr    mk_num ( const char * );

    //logical operators
    expr    mk_forall	( expr*, unsigned, expr );
    expr    mk_not  ( expr );
    expr    mk_and  ( expr *, unsigned );
    expr    mk_and  ( expr, expr );
    expr    mk_and  ( expr, expr, expr );
    expr    mk_or   ( expr *, unsigned );
    expr    mk_or   ( expr, expr );
    expr    mk_or   ( expr, expr, expr );
    expr    mk_ite  ( expr, expr, expr );

    //predicates
    expr    mk_eq   ( expr, expr );
    expr    mk_lt   ( expr, expr );
    expr    mk_leq  ( expr, expr );
    expr    mk_gt   ( expr, expr );
    expr    mk_geq  ( expr, expr );

    //functions
    expr    mk_plus ( expr *, unsigned );
    expr    mk_plus ( expr, expr );
    expr    mk_minus	( expr, expr );
    expr    mk_uminus	( expr );
    expr    mk_times	( expr *, unsigned );
    expr    mk_times	( expr, expr );
    expr    mk_div  ( expr, expr );
    expr    mk_abs  ( expr );
    expr    mk_exp  ( expr );
    expr    mk_log  ( expr );
    expr    mk_sqrt ( expr );
    expr    mk_pow  ( expr, expr );
    expr    mk_sin  ( expr );
    expr    mk_cos  ( expr );
    expr    mk_tan  ( expr );
    expr    mk_asin ( expr );
    expr    mk_acos ( expr );
    expr    mk_atan ( expr );
    expr    mk_sinh ( expr );
    expr    mk_cosh ( expr );
    expr    mk_tanh ( expr );
    expr    mk_atan2	( expr, expr );
    expr    mk_integral	( expr *, expr, expr, expr *, unsigned, const char *);
    void    define_ode	( const char *, expr *, expr *, unsigned);

    //min and max
    expr    mk_min  ( expr, expr );
    expr    mk_max  ( expr, expr );

    void    set_verbosity   ( int );
    void    set_precision   ( const double );
    double  get_precision   ();

    void    print   ( expr );
    void    reset   ();
    void    push    ();
    void    pop     ();

    void    declare  ( expr );
    result  check   ();
    result  check_assump    ( expr );
    result  check_lim_assump( expr , unsigned );

    unsigned	get_conflicts   ();
    unsigned    get_decisions   ();

    expr  get_value ( expr );
    double  get_domain_lb ( expr );
    double  get_domain_ub ( expr );
    void  set_domain_lb ( expr, double );
    void  set_domain_ub ( expr, double );
    double  get_lb  ( expr );
    double  get_ub  ( expr );

    result  get_bool_value  ( expr );

    //todo
    void    print_proof               ( const char * );
    void    print_interpolant         ( const char * );

private:
    env	m_context;
    std::vector<expr>    expr_table;
};

}



