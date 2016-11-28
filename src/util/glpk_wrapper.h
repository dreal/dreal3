/*********************************************************************
Author: Damien Zufferey <zufferey@csail.mit.edu>

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
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "./dreal_config.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/logging.h"

class Enode;

#ifdef USE_GLPK
#include "./glpk.h"

namespace dreal {

class glpk_wrapper {
private:
    // solver type
    enum solver_type_t { SIMPLEX, INTERIOR, EXACT };
    // for indexing variables
    box domain;
    // the lp
    glp_prob * lp;
    // whether to use simplex or interior point
    solver_type_t solver_type;
    // has the problem been changed since it was solved
    bool changed;

    unsigned get_index(Enode * e) const { return domain.get_index(e); }

    void set_constraint(int index, Enode * const e);

    void init_problem();

    double get_row_value(int row);

    bool check_unsat_error_kkt(double precision);

public:
    explicit glpk_wrapper(box const & b);
    glpk_wrapper(box const & b, std::unordered_set<Enode *> const & es);
    ~glpk_wrapper();

    bool is_sat();
    bool is_solution_unbounded();
    void get_solution(box & b);
    double get_objective();

    void set_domain(box const & b);
    const box & get_domain() const;

    void add(Enode * const e);
    void add(std::unordered_set<Enode *> const & es);

    void set_objective(Enode * const e);
    void set_minimize();
    void set_maximize();

    void get_error_bounds(double * errors);
    bool certify_unsat(double precision);

    void use_simplex();
    void use_interior_point();
    void use_exact();

    bool is_constraint_used(int index);

    int print_to_file(const char * fname);

    static bool is_linear(Enode * const e);
    static bool is_expr_linear(Enode * const e);
    static bool is_simple_bound(Enode * const e);
};

}  // namespace dreal
#endif
