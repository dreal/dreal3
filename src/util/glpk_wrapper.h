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
#include "./config.h"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/egraph/Enode.h"
#include "util/logging.h"
#include "util/box.h"

#ifdef USE_GLPK
#include "./glpk.h"

namespace dreal {

class glpk_wrapper {
private:
    // for indexing variables
    box domain;
    // the lp
    glp_prob *lp;
    // whether to use simplex or interior point
    bool simplex;

    unsigned get_index(Enode * e) const {
        return domain.get_index(e);
    }

    void set_constraint(int index, Enode * const e);

    void init_problem();

public:
    explicit glpk_wrapper(box const & b);
    glpk_wrapper(box const & b, std::unordered_set<Enode *> const & es);
    ~glpk_wrapper();

    bool is_sat();
    void get_solution(box & b);
    double get_objective();

    void set_domain(box const & b);
    void add(Enode * const e);
    void add(std::unordered_set<Enode *> const & es);

    void set_objective(Enode * const e);
    void set_minimize();
    void set_maximize();

    void use_simplex();
    void use_interior_point();

    int print_to_file(const char *fname);

    static bool is_linear(Enode * const e);
    static bool is_expr_linear(Enode * const e);
};
/*
    push: () → ()
    pop: () → ()
*/

}  // namespace dreal
#endif
