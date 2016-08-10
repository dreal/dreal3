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
#include "./config.h"

namespace dreal {

enum class Bool { False = -1, Undef, True };
enum class Logic { qf_nra, qf_nra_ode };
enum class vtype { Int, Real, Boolean };
using cexpr = void *;
using env = void *;

class solver;

class expr {
public:
    expr() {}
    expr(solver & s, char const *);  // so far it only works for declaring variables
    explicit expr(solver * s);
    expr(solver * const s, cexpr const);
    expr(solver * const s, expr * e);
    void set_ub(double const ub);
    void set_lb(double const lb);
    void set_bounds(double const lb, double const ub);
    void setContent(solver * s, cexpr c);
    std::string get_name();
    env const & get_ctx() const    { return cctx; }
    cexpr const &   get_cexpr() const  { return ep; }
    solver * get_solver() const { return m_solver; }
protected:
    solver * m_solver;
    env cctx;
    cexpr ep;
};

std::ostream & operator<<(std::ostream &, expr const &);
expr operator==(expr const & e1, expr const & e2);
expr operator==(expr const &, double const);
expr operator==(double const, expr const &);
expr operator>(expr const & e1, expr const & e2);
expr operator>(expr const &, double const);
expr operator>(double const, expr const &);
expr operator<(expr const & e1, expr const & e2);
expr operator<(expr const &, double const);
expr operator<(double const, expr const &);
expr operator<=(expr const & e1, expr const & e2);
expr operator<=(expr const &, double const);
expr operator<=(double const, expr const &);
expr operator>=(expr const & e1, expr const & e2);
expr operator>=(expr const &, double const);
expr operator>=(double const, expr const &);
expr operator+(expr const & e1, expr const & e2);
expr operator+(expr const &, double const);
expr operator+(double const, expr const &);
expr operator-(expr const & e1, expr const & e2);
expr operator-(double const, expr const &);
expr operator-(expr const &, double const);
expr operator-(expr const & e);
expr operator*(expr const & e1, expr const & e2);
expr operator*(expr const &, double const);
expr operator*(double const, expr const &);
expr operator/(expr const & e1, expr const & e2);
expr operator/(expr const &, double const);
expr operator/(double const, expr const &);
expr abs(expr const & e);
expr pow(expr const & e1, expr const & e2);
expr pow(expr const &, double const);
expr pow(double const, expr const &);
expr operator^(expr const &, double const);
expr operator^(double const, expr const &);
expr sqrt(expr const & e);
expr exp(expr const & e);
expr log(expr const & e);
expr sin(expr const & e);
expr cos(expr const & e);
expr tan(expr const & e);
expr asin(expr const & e);
expr acos(expr const & e);
expr atan(expr const & e);
expr sinh(expr const & e);
expr cosh(expr const & e);
expr tanh(expr const & e);
expr operator&&(expr const & e1, expr const & e2);
expr operator||(expr const & e1, expr const & e2);
expr operator!(expr const & e);
expr implies(expr const & e1, expr const & e2);
expr ite(expr const &, expr const &, expr const &);
expr der(expr const & e1, expr const & e2);
expr upoly(expr const & x, char const * a, unsigned const d);  // generates a univariate polynomial in the first argument; second argument sets the name of coefficients to be generated (will be indexed)
expr substitute(expr const & e, std::unordered_map<expr*, expr*> const & m);
expr substitute(expr const & e, std::vector<expr*> const & pre, std::vector<expr*> const & post);

class poly : public expr {
public:
    ~poly();
    poly(std::vector<expr*> &, char const *, unsigned);
    std::vector<expr*> &  getCofs() { return m_c; }
    void    resizeToDegree(unsigned);
    unsigned    getNumVar() { return m_x.size(); }
    unsigned    getNumCof() { return m_c.size(); }
    cexpr   buildExpr(char const *, unsigned);
    expr *  getExpr();
    void    setCofBounds(double, double);
private:
    unsigned    degree;
    expr *  m_e;
    std::vector<expr*> & m_x;  // variables
    std::vector<expr*>   m_c;  // coefficients
    std::vector<expr*>   m_m;  // monomials, not used as of Jun 23, 2016
};

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
    expr    get_value(expr const & e);
    expr *  new_var(char const *, double const, double const);
    expr *  new_ivar(char const *, int const, int const);
    expr *  new_var(char const *, vtype const);
    expr *  new_var(char const *);
    expr *  new_num(double const);
    void    set_verbose(bool const b);
    void    set_delta(double const d);
    void    set_polytope(bool const b = true);
#ifdef USE_GLPK
    void    set_lp(bool const b = true);
    void    set_lp_only(bool const b = true);
#endif
    void    set_simulation(bool const b = true);
    void    reset();
    void    push();
    void    pop();
    void    add(expr const & e);
    void    set_domain_lb(expr &, double const);
    void    set_domain_ub(expr &, double const);
    void    print_model(std::ostream & out = std::cerr);
    void    print_problem(std::ostream & out = std::cerr);
    void    print_infix(std::ostream & out = std::cerr);
    double  get_precision() const;
    double  get_domain_lb(expr const & e) const;
    double  get_domain_ub(expr const & e) const;
    double  get_lb(expr const & e) const;
    double  get_ub(expr const & e) const;
    double  get_value(expr const & e) const;
    bool    check();
    bool    solve();
    Bool  check_assump(expr const & e);
    Bool  check_lim_assump(expr const & , unsigned const);
    Bool  get_bool_value(expr const & e);
    unsigned get_conflicts();
    unsigned get_decisions();
    env     get_ctx() { return cctx; }
    std::vector<expr const *> const & get_vtab() { return vtab; }
    std::vector<double> const & get_stab() { return stab; }
    std::vector<expr const *> const & get_etab() { return etab; }
    std::ostream & dump_formulas(std::ostream & out) const;

private:
    env cctx;
    std::vector<expr const *> vtab;  // variable table
    std::vector<double> stab;        // solution table
    std::vector<expr const *> etab;  // added enode table
    std::vector<expr const *> ntab;  // constant table
};
}  // namespace dreal
