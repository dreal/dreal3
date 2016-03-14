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

using result = enum { False=-1, Undef, True };
using logic = enum { qf_nra, qf_nra_ode };
using vtype = enum { Int, Real, Bool };
using cexpr =  void *;
using env = void *;

class solver;

class expr {
public:
    expr(solver * const s, cexpr const e);
    env const &    get_ctx() const    { return cctx; }
    env            get_ctx()          { return cctx; }
    cexpr const &  get_cexpr() const  { return ep; }
    cexpr          get_cexpr()        { return ep; }
    solver *       get_solver() const { return s; }
    // solver *       get_solver()       { return s; }

private:
    solver * const s;
    env const      cctx;
    cexpr const    ep;
friend std::ostream & operator<<(std::ostream & out, expr const & e);
};

std::ostream & operator<<(std::ostream & out, expr const & e);

//All passing by value to make chained compositions easy. Delegating RVO to compilers.
expr operator==(expr const & e1, expr const & e2);
expr operator==(expr const & e1, double const a);
expr operator==(double const a, expr const & e1);
expr operator>(expr const & e1, expr const & e2);
expr operator>(expr const & e1, double const a);
expr operator>(double const a, expr const & e1);
expr operator<(expr const & e1, expr const & e2);
expr operator<(expr const & e1, double const a);
expr operator<(double const a, expr const & e1);
expr operator<=(expr const & e1, expr const & e2);
expr operator<=(expr const & e1, double const a);
expr operator<=(double const a, expr const & e1);
expr operator>=(expr const & e1, expr const & e2);
expr operator>=(expr const & e1, double const a);
expr operator>=(double const a, expr const & e1);
expr operator+(expr const & e1, expr const & e2);
expr operator+(expr const & e1, double const a);
expr operator+(double const a, expr const & e1);
expr operator-(expr const & e1, expr const & e2);
expr operator-(double const a, expr const & e1);
expr operator-(expr const & e1, double const a);
expr operator-(expr const & arg);
expr operator*(expr const & e1, expr const & e2);
expr operator*(expr const & e1, double const a);
expr operator*(double const a, expr const & e1);
expr operator/(expr const & e1, expr const & e2);
expr operator/(expr const & e1, double const a);
expr operator/(double const a, expr const & e1);
expr abs(expr const & arg);
expr pow(expr const & e1, expr const & e2);
expr pow(expr const & e1, double const a);
expr pow(double const a, expr const & e1);
expr operator^(expr const & e1, expr const & e2);
expr operator^(expr const & e1, double const a);
expr operator^(double const a, expr const & e1);
expr sqrt(expr const & arg);
expr exp(expr const & arg);
expr log(expr const & arg);
expr sin(expr const & arg);
expr cos(expr const & arg);
expr tan(expr const & arg);
expr asin(expr const & arg);
expr acos(expr const & arg);
expr atan(expr const & arg);
expr sinh(expr const & arg);
expr cosh(expr const & arg);
expr tanh(expr const & arg);
expr operator&&(expr const & e1, expr const & e2);
expr operator||(expr const & e1, expr const & e2);
expr operator!(expr const & arg);
expr implies(expr const & e1, expr const & e2);
expr ite(expr const & e1, expr const & e2, expr const & e3);

class solver {
public:
    solver();
    ~solver();

    expr    var(char const *);
    expr    var(char const *, vtype);
    expr    var(char const *, double, double);
    expr    var(char const *, int, int);
    expr    num(double const);
    expr    num(int const);
    expr    num(char const * const);
    expr    get_value(expr const &);

    void    set_verbosity(int const);
    void    set_precision(double const);
    void    reset();
    void    push();
    void    pop();
    void    add(expr const &);
    void    set_domain_lb(expr &, double const);
    void    set_domain_ub(expr &, double const);

    double  get_precision() const;
    double  get_domain_lb(expr const & e) const;
    double  get_domain_ub(expr const & e) const;
    double  get_lb(expr const & e) const;
    double  get_ub(expr const & e) const;

    bool    check();

    result  check_assump(expr const &);
    result  check_lim_assump(expr const & , unsigned const);
    result  get_bool_value(expr const &);

    unsigned get_conflicts();
    unsigned get_decisions();

    env     get_ctx() { return cctx; };

    //todo
    void    print_proof(char const *);
    void    print_interpolant(char const *);

private:
    env cctx;
    std::vector<expr>    expr_table;
};
}
