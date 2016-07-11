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

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdio>
#include <exception>
#include "./config.h"
#include "ibex/ibex.h"
#include "opensmt/common/LA.h"
#include "util/glpk_wrapper.h"
#include "util/logging.h"

#ifdef USE_GLPK

namespace dreal {

glpk_wrapper::glpk_wrapper(box const & b)
    : domain(b), lp(glp_create_prob()), solver_type(SIMPLEX), changed(true) {
    init_problem();
}

glpk_wrapper::glpk_wrapper(box const & b, std::unordered_set<Enode *> const & es)
    : domain(b), lp(glp_create_prob()), solver_type(SIMPLEX), changed(true) {
    init_problem();
    add(es);
}

glpk_wrapper::~glpk_wrapper() {
    glp_delete_prob(lp);
}

void glpk_wrapper::set_constraint(int index, Enode * const e) {
    DREAL_LOG_INFO << "glpk_wrapper::set_constraint  " << e << " with " << e->getPolarity();
    assert(is_linear(e));
    changed = true;
    LAExpression la(e);
    auto vars = e->get_vars();
    auto s = vars.size();
    auto indices = new int[s + 1];
    auto values = new double[s + 1];
    int i = 1;
    for (auto it = la.begin(); it != la.end(); ++it) {
        auto v = it->first;
        double c = it->second;
        if (v != nullptr && c != 0.0) {
            DREAL_LOG_INFO << "glpk_wrapper::set_constraint " << c << " * " << v;
            indices[i] = get_index(v) + 1;
            values[i] = c;
            i += 1;
        } else {
            if (e->isEq()) {
                assert(!e->hasPolarity() || e->getPolarity() != l_False);
                DREAL_LOG_INFO << "glpk_wrapper::set_constraint == " << c;
                glp_set_row_bnds(lp, index, GLP_FX, -c, -c);
            } else {
                if (!e->hasPolarity() || e->getPolarity() != l_False) {
                    DREAL_LOG_INFO << "glpk_wrapper::set_constraint <= " << (-c);
                    glp_set_row_bnds(lp, index, GLP_UP, 0, -c);
                } else {
                    DREAL_LOG_INFO << "glpk_wrapper::set_constraint >= " << (-c);
                    glp_set_row_bnds(lp, index, GLP_LO, -c, 0);
                }
            }
        }
    }
    glp_set_mat_row(lp, index, i-1, indices, values);
    delete[] indices;
    delete[] values;
    // name the constraints (helps debugging)
    if (DREAL_LOG_INFO_IS_ON) {
        std::ostringstream stream;
        if (e->getPolarity() == l_False) {
            stream << "¬";
        }
        stream << e;
        glp_set_row_name(lp, index, stream.str().c_str());
    }
}

void glpk_wrapper::init_problem() {
    // use minimzation by default
    glp_set_obj_dir(lp, GLP_MIN);
    // create as many col as dimension in b
    glp_add_cols(lp, domain.size());
    // name the variables (helps debugging)
    if (DREAL_LOG_INFO_IS_ON) {
        for (unsigned int i = 0; i < domain.size(); i++) {
            glp_set_col_name(lp, i+1, domain.get_name(i).c_str());
        }
    }
    //
    set_domain(domain);
}

void glpk_wrapper::set_domain(box const & b) {
    assert(!b.is_empty());
    changed = true;
    domain = b;
    for (unsigned int i = 0; i < b.size(); i++) {
        auto interval = b[i];
        double lb = interval.lb();
        double ub = interval.ub();
        if (lb == NEG_INFINITY) {
            if (ub == POS_INFINITY) {
                glp_set_col_bnds(lp, i+1, GLP_FR, lb, ub);
            } else {
                glp_set_col_bnds(lp, i+1, GLP_UP, lb, ub);
            }
        } else {
            if (ub == POS_INFINITY) {
                glp_set_col_bnds(lp, i+1, GLP_LO, lb, ub);
            } else {
                if (lb == ub) {
                    glp_set_col_bnds(lp, i+1, GLP_FX, lb, ub);
                } else {
                    glp_set_col_bnds(lp, i+1, GLP_DB, lb, ub);
                }
            }
        }
    }
}

const box& glpk_wrapper::get_domain() const {
    return domain;
}

void glpk_wrapper::add(Enode * const e) {
    int idx = glp_add_rows(lp, 1);
    set_constraint(idx, e);
}

void glpk_wrapper::add(std::unordered_set<Enode *> const & es) {
    int idx = glp_add_rows(lp, es.size());
    for (auto it = es.cbegin(); it != es.cend(); ++it) {
        set_constraint(idx, *it);
        idx += 1;
    }
}

bool glpk_wrapper::is_sat() {
    if (solver_type == SIMPLEX || solver_type == EXACT) {
        int status = glp_get_status(lp);
        if (status == GLP_UNDEF || changed) {
            glp_smcp parm;
            glp_init_smcp(&parm);
            parm.msg_lev = GLP_MSG_OFF;
            // always try first the normal simple (get close to an optimal solution in double precision)
            int solved = glp_simplex(lp, &parm);
            // TODO(dzufferey) should we always fall back on exact when the normal simplex failed ?
            if (solver_type == EXACT || solved != 0) {
                solved = glp_exact(lp, &parm);
            }
            if (solved != 0) {
                switch (solved) {
                    case GLP_EBADB:
                        throw std::runtime_error("GLPK simplex failed: GLP_EBADB");
                    case GLP_ESING:
                        throw std::runtime_error("GLPK simplex failed: GLP_ESING");
                    case GLP_ECOND:
                        throw std::runtime_error("GLPK simplex failed: GLP_ECOND");
                    case GLP_EBOUND:
                        throw std::runtime_error("GLPK simplex failed: GLP_EBOUND");
                    case GLP_EFAIL:
                        throw std::runtime_error("GLPK simplex failed: GLP_EFAIL");
                    case GLP_EOBJLL:
                        throw std::runtime_error("GLPK simplex failed: GLP_EOBJLL");
                    case GLP_EOBJUL:
                        throw std::runtime_error("GLPK simplex failed: GLP_EOBJUL");
                    case GLP_EITLIM:
                        throw std::runtime_error("GLPK simplex failed: GLP_EITLIM");
                    case GLP_ETMLIM:
                        throw std::runtime_error("GLPK simplex failed: GLP_ETMLIM");
                    case GLP_ENOPFS:
                        throw std::runtime_error("GLPK simplex failed: GLP_ENOPFS");
                    case GLP_ENODFS:
                        throw std::runtime_error("GLPK simplex failed: GLP_ENODFS");
                    default:
                        throw std::runtime_error("GLPK simplex failed");
                }
            }
            status = glp_get_status(lp);
            changed = false;
        }
        return (status == GLP_OPT || status == GLP_FEAS || status == GLP_UNBND);
    } else {
        assert(solver_type == INTERIOR);
        int status = glp_ipt_status(lp);
        if (status == GLP_UNDEF || changed) {
            glp_iptcp parm;
            glp_init_iptcp(&parm);
            parm.msg_lev = GLP_MSG_OFF;
            int solved = glp_interior(lp, &parm);
            if (solved != 0) {
                switch (solved) {
                    case GLP_EFAIL:
                        throw std::runtime_error("GLPK interior-point failed: GLP_EFAIL");
                    case GLP_ENOCVG:
                        throw std::runtime_error("GLPK interior-point failed: GLP_ENOCVG");
                    case GLP_EOBJUL:
                        throw std::runtime_error("GLPK interior-point failed: GLP_EOBJUL");
                    case GLP_EITLIM:
                        throw std::runtime_error("GLPK interior-point failed: GLP_EITLIM");
                    case GLP_EINSTAB:
                        throw std::runtime_error("GLPK interior-point failed: GLP_EINSTAB");
                    default:
                        throw std::runtime_error("GLPK interior-point failed");
                }
            }
            status = glp_ipt_status(lp);
            changed = false;
        }
        return status == GLP_OPT;
    }
}

void glpk_wrapper::get_solution(box & b) {
    assert(is_sat());
    for (unsigned int i = 0; i < b.size(); i++) {
        if (solver_type == SIMPLEX || solver_type == EXACT) {
            b[i] = glp_get_col_prim(lp, i+1);
        } else {
            assert(solver_type == INTERIOR);
            b[i] = glp_ipt_col_prim(lp, i+1);
        }
    }
}

double glpk_wrapper::get_objective() {
    assert(is_sat());
    if (solver_type == SIMPLEX || solver_type == EXACT) {
        return glp_get_obj_val(lp);
    } else {
        assert(solver_type == INTERIOR);
        return glp_ipt_obj_val(lp);
    }
}

void glpk_wrapper::set_objective(Enode * const e) {
    changed = true;
    for (unsigned int i = 1; i <= domain.size(); i++) {
        glp_set_obj_coef(lp, i, 0);
    }
    if (e != nullptr) {
        assert(is_expr_linear(e));
        LAExpression la(e);
        for (auto it = la.begin(); it != la.end(); ++it) {
            auto v = it->first;
            auto c = it->second;
            if (v != nullptr) {
                glp_set_obj_coef(lp, get_index(v) + 1, c);
            }
        }
    }
}

void glpk_wrapper::set_minimize() {
    changed = true;
    glp_set_obj_dir(lp, GLP_MIN);
}

void glpk_wrapper::set_maximize() {
    changed = true;
    glp_set_obj_dir(lp, GLP_MAX);
}

double glpk_wrapper::get_row_value(int i) {
    double cstr_value = 0;
    if (solver_type ==  SIMPLEX || solver_type == EXACT) {
        int cstr_status = glp_get_row_stat(lp, i);
        if (cstr_status == GLP_BS) {  // basic variable;
            cstr_status = glp_get_row_prim(lp, i);  // or glp_get_row_dual
        } else if (cstr_status == GLP_NL || cstr_status == GLP_NS) {  // non-basic variable on its lower bound, non-basic fixed variable.
            cstr_value = glp_get_row_lb(lp, i);
        } else if (cstr_status == GLP_NU) {  //  non-basic variable on its upper bound
            cstr_value = glp_get_row_ub(lp, i);
        }
        // TODO(dzufferey): should we do something for GLP_NF — non-basic free (unbounded) variable;
    } else {
        cstr_value = glp_ipt_row_prim(lp, i);  // or glp_ipt_row_dual
    }
    return cstr_value;
}

bool glpk_wrapper::check_unsat_error_kkt(double precision) {
    double ae_max_1;  // largest absolute error
    int ae_ind_1;     // number of row the largest absolute error
    double re_max_1;  // largest relative error
    int re_ind_1;     // number of row with the largest relative error

    double ae_max_2;  // largest absolute error
    int ae_ind_2;     // variable with the largest absolute error
    double re_max_2;  // largest relative error
    int re_ind_2;     // variable with the largest relative error

    int sol;
    if (solver_type == SIMPLEX || solver_type == EXACT) {
        sol = GLP_SOL;
    } else {
        sol = GLP_IPT;
    }

    // check primal equality constraints
    glp_check_kkt(lp, sol, GLP_KKT_PE, &ae_max_1, &ae_ind_1, &re_max_1, &re_ind_1);

    // check primal bound constraints
    glp_check_kkt(lp, sol, GLP_KKT_PB, &ae_max_2, &ae_ind_2, &re_max_2, &re_ind_2);

    return ae_max_1 < precision && ae_max_1 < ae_max_2;
}

void glpk_wrapper::get_error_bounds(double * errors) {
    int n = domain.size();
    int * nbr_non_zero = new int[n];
    for (int i = 0; i < n; i++) {
        errors[i] = INFINITY;
        nbr_non_zero[i] = 0;
    }

    // get the error on the KKT condition
    int sol;
    if (solver_type == SIMPLEX || solver_type == EXACT) {
        sol = GLP_SOL;
    } else {
        sol = GLP_IPT;
    }

    double ae_max;  // largest absolute error
    int ae_ind;     // number of row (PE), column (DE), or variable (PB, DB) with the largest absolute error
    double re_max;  // largest relative error
    int re_ind;     // number of row (PE), column (DE), or variable (PB, DB) with the largest relative error

    // GLP_KKT_PE — check primal equality constraints
    glp_check_kkt(lp, sol, GLP_KKT_PE, &ae_max, &ae_ind, &re_max, &re_ind);

    // a sparse vector for the coeffs in the row
    int row_size = 1;
    int * row_idx = new int[n + 1];
    double * row_coeff = new double[n + 1];

    // PE
    //  gives the distance between the auxiliary var and A * strucutral variable
    int m = glp_get_num_rows(lp);
    for (int i = 1; i <= m ; ++i) {
        // get the coeffs for that constraint
        row_size = glp_get_mat_row(lp, i, row_idx, row_coeff);
        for (int j = 1; j <= row_size; j++) {
            int v = row_idx[j] - 1;  // GLPK indexing
            nbr_non_zero[v] += 1;
            int c = row_coeff[j];
            // relative error
            errors[v] = std::min(errors[v], get_row_value(i) * re_max / c);
            // absolute error
            errors[v] = std::min(errors[v], ae_max / c);
        }
    }

    // variables that don't matter
    for (int i = 0; i < n; i++) {
        if (nbr_non_zero[i] == 0) {
            errors[i] = 0;
        }
        DREAL_LOG_INFO << "glpk_wrapper::get_error_bounds: error for " << domain.get_name(i) << " is " << errors[i];
    }

    delete[] nbr_non_zero;
    delete[] row_idx;
    delete[] row_coeff;
}

bool glpk_wrapper::certify_unsat(double precision) {
    // cheaper check using on the the KKT conditions
    return check_unsat_error_kkt(precision);
}

void glpk_wrapper::use_simplex() {
    solver_type = SIMPLEX;
    changed = true;
}

void glpk_wrapper::use_interior_point() {
    solver_type = INTERIOR;
    changed = true;
}

void glpk_wrapper::use_exact() {
    solver_type = EXACT;
    changed = true;
}

bool glpk_wrapper::is_constraint_used(int index) {
    if (solver_type ==  SIMPLEX || solver_type == EXACT) {
        return glp_get_row_stat(lp, index + 1) == GLP_BS;
    } else {
        return true;
    }
}

int glpk_wrapper::print_to_file(const char *fname) {
    return glp_write_lp(lp, nullptr, fname);
}

bool is_expr_linear_product(Enode * const t, bool * saw_variable) {
    if (t->isConstant()) {
        return true;
    } else if (t->isVar()) {
        if (*saw_variable) {
            return false;
        } else {
            *saw_variable = true;
            return true;
        }
    } else if ( t->isPlus() || t->isMinus() || t->isUminus()) {
        bool old_saw = *saw_variable;
        bool new_saw = false;
        for (Enode * arg_list = t->getCdr(); !arg_list->isEnil(); arg_list = arg_list->getCdr()) {
            bool child_linear = is_expr_linear_product(arg_list->getCar(), saw_variable);
            if (!child_linear) {
                return false;
            }
            new_saw = *saw_variable;
            *saw_variable = old_saw;
        }
        *saw_variable = new_saw;
        return true;
    } else if ( t->isTimes() ) {
        for ( Enode * arg_list = t->getCdr( )
            ; !arg_list->isEnil( )
            ; arg_list = arg_list->getCdr( ) )
        {
            Enode * arg = arg_list->getCar( );
            if (!is_expr_linear_product(arg, saw_variable)) {
                return false;
            }
        }
        return true;
    } else {
        return false;
    }
}

bool glpk_wrapper::is_expr_linear(Enode * const t) {
    bool saw = false;
    return is_expr_linear_product(t, &saw);
}

bool glpk_wrapper::is_linear(Enode * const e) {
    bool is_eq = e->isEq() && (!e->hasPolarity() || e->getPolarity() != l_False);
    return
        (is_eq || e->isLeq()) &&
        is_expr_linear(e->get1st()) &&
        is_expr_linear(e->get2nd());
}

bool only_one_var(Enode * const t, Enode const * * seen) {
    if ( t->isConstant() ) {
        return true;
    } else if ( t->isVar() ) {
        if (*seen == nullptr) {
            *seen = t;
            return true;
        } else {
            return t == *seen;
        }
    } else if ( t->isPlus() || t->isTimes() || t->isMinus() ) {
        for (Enode * arg_list = t->getCdr(); !arg_list->isEnil(); arg_list = arg_list->getCdr()) {
            if (!only_one_var(arg_list->getCar(), seen)) {
                return false;
            }
        }
        return true;
    } else if ( t->isUminus() ) {
        return only_one_var(t->get1st(), seen);
    } else if ( t->isEq() || t->isLeq() || t->isLt() ) {
        return only_one_var(t->get1st(), seen) && only_one_var(t->get2nd(), seen);
    } else {
        return false;
    }
}


bool glpk_wrapper::is_simple_bound(Enode * const e) {
    Enode const * seen = nullptr;
    return is_linear(e) && only_one_var(e, &seen);
}

}  // namespace dreal
#endif
