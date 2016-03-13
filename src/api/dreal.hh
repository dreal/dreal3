#pragma once

#include <iostream>
#include <vector>
#include <utility>
#include <string>
#include <list>
#include <assert.h>

namespace dreal {

typedef enum { False=-1, Undef, True } result;
typedef enum { qf_nra, qf_nra_ode } logic;
typedef enum { Int, Real, Bool } vtype;

typedef void * cexpr;
typedef void * env;

class solver;

class expr {

public:

    expr( solver* s, cexpr e );
    inline env	get_ctx() { return cctx; }
    inline cexpr   get_cexpr() { return ep; }
    inline solver * get_solver() { return s; }

private:
    solver * s;
    env	    cctx;
    cexpr   ep;

};

//All passing by value to make chained compositions easy. Delegating RVO to compilers. 
expr operator==(expr, expr);
expr operator==( expr, double );
expr operator==( double, expr );
expr operator>(expr, expr);
expr operator>( expr, double );
expr operator>( double, expr );
expr operator<(expr, expr);
expr operator<( expr, double );
expr operator<( double, expr );
expr operator<=(expr, expr);
expr operator<=( expr, double );
expr operator<=( double, expr );
expr operator>=(expr, expr);
expr operator>=( expr, double );
expr operator>=( double, expr );
expr operator+( expr, expr );
expr operator+( expr, double );
expr operator+( double, expr );
expr operator-( expr, expr );
expr operator-( double, expr );
expr operator-( expr, double );
expr operator-( expr );
expr operator*( expr, expr );
expr operator*( expr, double );
expr operator*( double, expr );
expr operator/( expr, expr );
expr operator/( expr, double );
expr operator/( double, expr );
expr abs( expr );
expr pow( expr, expr );
expr pow( expr, double );
expr pow( double, expr );
expr operator^( expr, expr);
expr operator^( expr, double);
expr operator^( double, expr);
expr sqrt( expr );
expr exp( expr );
expr log( expr );
expr sin( expr );
expr cos( expr );
expr tan( expr );
expr asin( expr );
expr acos( expr );
expr atan( expr );
expr sinh( expr );
expr cosh( expr );
expr tanh( expr );
expr operator&&( expr, expr );
expr operator||( expr, expr );
expr operator!(expr);
expr implies(expr, expr);
expr ite(expr, expr, expr);

class solver {

public:

    solver();
    ~solver();

    expr    var(char const *);
    expr    var(char const *, vtype);
    expr    var(char const *, double, double);
    expr    var(char const *, int, int);
    expr    num(const double);
    expr    num(const int);
    expr    num(const char *);
    expr    get_value ( expr& );

    void    set_verbosity   ( int );
    void    set_precision   ( const double );
    void    print   ( expr& );
    void    reset   ();
    void    push    ();
    void    pop	    ();
    void    add	    ( expr& );
    void    set_domain_lb ( expr&, double );
    void    set_domain_ub ( expr&, double );
 
    double  get_precision   ();
    double  get_domain_lb ( expr& );
    double  get_domain_ub ( expr& );
    double  get_lb  ( expr& );
    double  get_ub  ( expr& );
 
    bool    check   ();

    result  check_assump    ( expr& );
    result  check_lim_assump( expr& , unsigned );
    result  get_bool_value  ( expr& );

    unsigned	get_conflicts   ();
    unsigned	get_decisions   ();
  
    inline  env	    get_ctx() { return cctx; }; 

    //todo
    void    print_proof               ( const char * );
    void    print_interpolant         ( const char * );

private:

    env cctx;
    std::vector<expr>    expr_table;

};


}



