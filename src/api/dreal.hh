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
    expr(solver* s, cexpr e);
    env const &    get_ctx() const    { return cctx; }
    env            get_ctx()          { return cctx; }
    cexpr const &  get_cexpr() const  { return ep; }
    cexpr          get_cexpr()        { return ep; }
    solver const * get_solver() const { return s; }
    solver *       get_solver()       { return s; }

private:
    solver * s;
    env      cctx;
    cexpr    ep;
friend std::ostream & operator<<(std::ostream & out, expr const & e);
};

std::ostream & operator<<(std::ostream & out, expr const & e);

//All passing by value to make chained compositions easy. Delegating RVO to compilers.
expr operator==(expr, expr);
expr operator==( expr, double );
expr operator==(double, expr );
expr operator>(expr, expr);
expr operator>(expr, double );
expr operator>(double, expr );
expr operator<(expr, expr);
expr operator<(expr, double );
expr operator<(double, expr );
expr operator<=(expr, expr);
expr operator<=(expr, double );
expr operator<=(double, expr );
expr operator>=(expr, expr);
expr operator>=(expr, double );
expr operator>=(double, expr );
expr operator+(expr, expr );
expr operator+(expr, double );
expr operator+(double, expr );
expr operator-(expr, expr );
expr operator-(double, expr );
expr operator-(expr, double );
expr operator-(expr );
expr operator*(expr, expr );
expr operator*(expr, double );
expr operator*(double, expr );
expr operator/(expr, expr );
expr operator/(expr, double );
expr operator/(double, expr );
expr abs(expr );
expr pow(expr, expr );
expr pow(expr, double );
expr pow(double, expr );
expr operator^(expr, expr);
expr operator^(expr, double);
expr operator^(double, expr);
expr sqrt(expr );
expr exp(expr );
expr log(expr );
expr sin(expr );
expr cos(expr );
expr tan(expr );
expr asin(expr );
expr acos(expr );
expr atan(expr );
expr sinh(expr );
expr cosh(expr );
expr tanh(expr );
expr operator&&(expr, expr );
expr operator||(expr, expr );
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
    expr    get_value (expr&);

    void    set_verbosity   (int);
    void    set_precision   (const double);
    void    reset   ();
    void    push    ();
    void    pop     ();
    void    add     (expr&);
    void    set_domain_lb (expr&, double);
    void    set_domain_ub (expr&, double);

    double  get_precision   ();
    double  get_domain_lb (expr&);
    double  get_domain_ub (expr&);
    double  get_lb  (expr&);
    double  get_ub  (expr&);

    bool    check   ();

    result  check_assump    (expr&);
    result  check_lim_assump(expr& , unsigned);
    result  get_bool_value  (expr&);

    unsigned	get_conflicts   ();
    unsigned	get_decisions   ();

    env     get_ctx() { return cctx; };

    //todo
    void    print_proof               (const char *);
    void    print_interpolant         (const char *);

private:
    env cctx;
    std::vector<expr>    expr_table;
};
}
