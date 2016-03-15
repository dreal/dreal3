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

#include <iostream>
#include <vector>
#include <utility>
#include <string>
#include <list>
#include <assert.h>

namespace dreal {

enum class Bool { False=-1, Undef, True };
enum class Logic { qf_nra, qf_nra_ode };
enum class vtype { Int, Real, Bool };
using cexpr = void *;
using env = void *;

class solver;

class expr {
public:
    expr(solver * const s, cexpr const e);
    void    set_ub(double);
    void    set_lb(double);
    void    set_bounds(double, double);
    env const &    get_ctx() const    { return cctx; }
    cexpr const &  get_cexpr() const  { return ep; }
    solver *       get_solver() const { return s; }
private:
    solver * const s;
    env const      cctx;
    cexpr const    ep;
friend std::ostream & operator<<(std::ostream & out, expr const & e);
};

std::ostream & operator<<(std::ostream & out, expr const & e);
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
    std::vector<expr>    var_vec(char const *, unsigned);
    void    set_verbosity(int const);
    void    set_precision(double const);
    void    reset();
    void    push();
    void    pop();
    void    add(expr &);
    void    set_domain_lb(expr &, double const);
    void    set_domain_ub(expr &, double const);
    void    print_model();
    void    print_problem();
    double  get_precision() const;
    double  get_domain_lb(expr const &) const;
    double  get_domain_ub(expr const &) const;
    double  get_lb(expr const &) const;
    double  get_ub(expr const &) const;
    double  get_value(expr const &) const; 
    bool    check();
    Bool  check_assump(expr const &);
    Bool  check_lim_assump(expr const & , unsigned const);
    Bool  get_bool_value(expr const &);
    unsigned get_conflicts();
    unsigned get_decisions();
    env     get_ctx() { return cctx; }
    std::vector<expr*>	const &	get_vtab() { return vtab; }
    std::vector<double> const &	get_stab() { return stab; }
    std::vector<expr*>	const & get_etab() { return etab; }
    //todo
    void    print_proof(char const *);
    void    print_interpolant(char const *);
private:
    env cctx;
    std::vector<expr*>	vtab;
    std::vector<double>	stab;
    std::vector<expr*>	etab;
};
}
