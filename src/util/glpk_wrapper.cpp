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

#include <cstdio>
#include <cassert>
#include <exception>
#include "opensmt/common/LA.h"
#include "util/glpk_wrapper.h"
#include "ibex/ibex.h"

#ifdef USE_GLPK

namespace dreal {

glpk_wrapper::glpk_wrapper(box const & b)
    : domain(b), lp(glp_create_prob()), simplex(true) {
    init_problem();
}

glpk_wrapper::glpk_wrapper(box const & b, std::unordered_set<Enode *> const & es)
    : domain(b), lp(glp_create_prob()), simplex(true) {
    init_problem();
    add(es);
}

glpk_wrapper::~glpk_wrapper() {
    glp_delete_prob(lp);
}

void glpk_wrapper::set_constraint(int index, Enode * const e) {
    assert(is_linear(e));
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
            indices[i] = get_index(v) + 1;
            values[i] = c;
            i += 1;
        } else {
            if (e->isEq()) {
                assert(!e->hasPolarity() || e->getPolarity() != l_False);
                glp_set_row_bnds(lp, index, GLP_FX, -c, -c);
            } else {
                if (!e->hasPolarity() || e->getPolarity() != l_False) {
                    glp_set_row_bnds(lp, index, GLP_UP, 0, -c);
                } else {
                    glp_set_row_bnds(lp, index, GLP_LO, 0, -c);
                }
            }
        }
    }
    glp_set_mat_row(lp, index, i-1, indices, values);
    delete[] indices;
    delete[] values;
}

void glpk_wrapper::init_problem() {
    // use minimzation by default
    glp_set_obj_dir(lp, GLP_MIN);
    // create as many col as dimension in b
    glp_add_cols(lp, domain.size());
    //
    set_domain(domain);
}

void glpk_wrapper::set_domain(box const & b) {
    assert(!b.is_empty());
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
    for (auto it = es.begin(); it != es.end(); ++it) {
        set_constraint(idx, *it);
        idx += 1;
    }
}

bool glpk_wrapper::is_sat() {
    if (simplex) {
        int status = glp_get_status(lp);
        if (status == GLP_UNDEF) {
            glp_smcp parm;
            glp_init_smcp(&parm);
            parm.msg_lev = GLP_MSG_OFF;
            int solved = glp_simplex(lp, &parm);
            if (solved != 0) {
                throw std::runtime_error("GLPK simplex failed");
            }
            status = glp_get_status(lp);
        }
        return (status == GLP_OPT || status == GLP_FEAS || status == GLP_UNBND);
    } else {
        int status = glp_ipt_status(lp);
        if (status == GLP_UNDEF) {
            glp_iptcp parm;
            glp_init_iptcp(&parm);
            parm.msg_lev = GLP_MSG_OFF;
            int solved = glp_interior(lp, &parm);
            if (solved != 0) {
                throw std::runtime_error("GLPK interior-point failed");
            }
            status = glp_ipt_status(lp);
        }
        return status == GLP_OPT;
    }
}

void glpk_wrapper::get_solution(box & b) {
    assert(is_sat());
    for (unsigned int i = 0; i < b.size(); i++) {
        if (simplex) {
            b[i] = glp_get_col_prim(lp, i+1);
        } else {
            b[i] = glp_ipt_col_prim(lp, i+1);
        }
    }
}

double glpk_wrapper::get_objective() {
    assert(is_sat());
    if (simplex) {
        return glp_get_obj_val(lp);
    } else {
        return glp_ipt_obj_val(lp);
    }
}

void glpk_wrapper::set_objective(Enode * const e) {
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

void glpk_wrapper::set_minimize() {
    glp_set_obj_dir(lp, GLP_MIN);
}

void glpk_wrapper::set_maximize() {
    glp_set_obj_dir(lp, GLP_MAX);
}

void glpk_wrapper::use_simplex() {
    simplex = true;
}

void glpk_wrapper::use_interior_point() {
    simplex = false;
}

int glpk_wrapper::print_to_file(const char *fname) {
    return glp_write_lp(lp, nullptr, fname);
}

bool glpk_wrapper::is_expr_linear(Enode * const t) {
    if ( t->isPlus() ) {
        for (Enode * arg_list = t->getCdr(); !arg_list->isEnil(); arg_list = arg_list->getCdr()) {
            if (!is_expr_linear(arg_list->getCar())) {
                return false;
            }
        }
        return true;
    } else if ( t->isTimes() ) {
        Enode * x = t->get1st();
        Enode * y = t->get2nd();
        if ( x->isConstant() ) {
            return is_expr_linear(y);
        } else if ( y->isConstant() ) {
            return is_expr_linear(x);
        } else {
            return false;
        }
    } else {
        return t->isVar() || t->isConstant();
    }
}

bool glpk_wrapper::is_linear(Enode * const e) {
    return
        (e->isEq() || e->isLeq()) &&
        is_expr_linear(e->get1st()) &&
        is_expr_linear(e->get2nd());
}

}  // namespace dreal
#endif
