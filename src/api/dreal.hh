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

#include <functional>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

namespace dreal {

enum class Bool { False = -1, Undef, True };
enum class Logic { qf_nra, qf_nra_ode };
enum class vtype { Int, Real, Boolean };
using cexpr = void *;
using env = void *;

class solver;

class expr {
public:
    expr();
    expr(solver &, char const *);  // so far it only works for declaring variables
    expr(solver * const, cexpr const);
    expr(solver * const, expr *);
    void    set_ub(double const);
    void    set_lb(double const);
    void    set_bounds(double const, double const);
    std::string get_name();
    env const & get_ctx() const    { return cctx; }
    cexpr const &   get_cexpr() const  { return ep; }
    solver *    get_solver() const { return m_solver; }
private:
    solver *    m_solver;
    env cctx;
    cexpr   ep;
};

std::ostream & operator<<(std::ostream &, expr const &);
expr operator==(expr const &, expr const &);
expr operator==(expr const &, double const);
expr operator==(double const, expr const &);
expr operator>(expr const &, expr const &);
expr operator>(expr const &, double const);
expr operator>(double const, expr const &);
expr operator<(expr const &, expr const &);
expr operator<(expr const &, double const);
expr operator<(double const, expr const &);
expr operator<=(expr const &, expr const &);
expr operator<=(expr const &, double const);
expr operator<=(double const, expr const &);
expr operator>=(expr const &, expr const &);
expr operator>=(expr const &, double const);
expr operator>=(double const, expr const &);
expr operator+(expr const &, expr const &);
expr operator+(expr const &, double const);
expr operator+(double const, expr const &);
expr operator-(expr const &, expr const &);
expr operator-(double const, expr const &);
expr operator-(expr const &, double const);
expr operator-(expr const &);
expr operator*(expr const &, expr const &);
expr operator*(expr const &, double const);
expr operator*(double const, expr const &);
expr operator/(expr const &, expr const &);
expr operator/(expr const &, double const);
expr operator/(double const, expr const &);
expr abs(expr const &);
expr pow(expr const &, expr const &);
expr pow(expr const &, double const);
expr pow(double const, expr const &);
expr operator^(expr const &, double const);
expr operator^(double const, expr const &);
expr sqrt(expr const &);
expr exp(expr const &);
expr log(expr const &);
expr sin(expr const &);
expr cos(expr const &);
expr tan(expr const &);
expr asin(expr const &);
expr acos(expr const &);
expr atan(expr const &);
expr sinh(expr const &);
expr cosh(expr const &);
expr tanh(expr const &);
expr operator&&(expr const &, expr const &);
expr operator||(expr const &, expr const &);
expr operator!(expr const &);
expr implies(expr const &, expr const &);
expr ite(expr const &, expr const &, expr const &);
expr der(expr const &, expr const &);
expr upoly(expr const &, char const *, unsigned);
expr substitute(expr const &, std::unordered_map<expr*, expr*> const &);
expr substitute(expr const &, std::vector<expr*> const &, std::vector<expr*> const &);

class solver {
public:
    solver();
    ~solver();
    expr    var(char const *);
    expr    var(char const *, vtype const);
    expr    var(char const *, double const, double const);
    expr    ivar(char const *, int const, int const);
    expr    num(double const);
    expr    num(int const);
    expr    num(char const * const);
    expr    get_value(expr const &);
    expr *  new_var(char const *, double const, double const);
    expr *  new_ivar(char const *, int const, int const);
    expr *  new_var(char const *, vtype const);
    expr *  new_var(char const *);
    expr *  new_num(double const);
    void    set_verbose(bool const b);
    void    set_delta(double const d);
    void    set_polytope();
    void    set_simulation();
    void    reset();
    void    push();
    void    pop();
    void    add(expr const &);
    void    set_domain_lb(expr &, double const);
    void    set_domain_ub(expr &, double const);
    void    print_model(std::ostream & out = std::cerr);
    void    print_problem(std::ostream & out = std::cerr);
    void    print_infix(std::ostream & out = std::cerr);
    double  get_precision() const;
    double  get_domain_lb(expr const &) const;
    double  get_domain_ub(expr const &) const;
    double  get_lb(expr const &) const;
    double  get_ub(expr const &) const;
    double  get_value(expr const &) const;
    bool    check();
    bool    solve();
    Bool  check_assump(expr const &);
    Bool  check_lim_assump(expr const & , unsigned const);
    Bool  get_bool_value(expr const &);
    unsigned get_conflicts();
    unsigned get_decisions();
    env     get_ctx() { return cctx; }
    std::vector<expr const *> const & get_vtab() { return vtab; }
    std::vector<double> const & get_stab() { return stab; }
    std::vector<expr const *> const & get_etab() { return etab; }

private:
    env cctx;
    std::vector<expr const *> vtab;  // variable table
    std::vector<double> stab;        // solution table
    std::vector<expr const *> etab;  // added enode table
    std::vector<expr const *> ntab;  // constant table
};
}  // namespace dreal
