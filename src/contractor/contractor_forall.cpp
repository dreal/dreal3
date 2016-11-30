/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

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

#include "contractor/contractor_forall.h"

#include <cassert>
#include <cstddef>
#include <deque>
#include <exception>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <iterator>
#include <limits>
#include <memory>
#include <queue>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "./dreal_config.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "ibex/ibex.h"
#include "icp/mcss_icp.h"
#include "interval/interval.icc"
#include "minisat/core/SolverTypes.h"
#include "opensmt/egraph/Enode.h"
#include "smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/enode_utils.h"
#include "util/eval.h"
#include "util/logging.h"
#include "util/scoped_vec.h"
#include "util/stat.h"
#include "util/strategy.h"
#include "util/thread_local.h"

class Egraph;
#ifdef USE_NLOPT
#include "nlopt.hpp"
#endif

using std::back_inserter;
using std::boolalpha;
using std::cerr;
using std::endl;
using std::exception;
using std::function;
using std::get;
using std::initializer_list;
using std::make_shared;
using std::move;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::queue;
using std::runtime_error;
using std::set;
using std::shared_ptr;
using std::string;
using std::tuple;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {

static unordered_map<Enode *, ibex::Interval> make_subst_from_value(
    box const & b, unordered_set<Enode *> const & vars) {
    unordered_map<Enode *, ibex::Interval> subst;
    for (Enode * const var : vars) {
        auto value = b[var];
        subst.emplace(var, value);
    }
    return subst;
}

contractor_forall::contractor_forall(box const & b, shared_ptr<forall_constraint> const ctr)
    : contractor_cell(contractor_kind::FORALL, extract_bitset(b, ctr)), m_ctr(ctr) {}

ibex::BitSet contractor_forall::extract_bitset(box const & b,
                                               std::shared_ptr<forall_constraint> const ctr) {
    ibex::BitSet ret{ibex::BitSet::empty(b.size())};
    for (Enode * var : ctr->get_body()->get_exist_vars()) {
        ret.add(b.get_index(var));
    }
    return ret;
}

void contractor_forall::prune_tree(contractor_status & cs, Enode * body, bool const p) {
    if (body->isOr()) {
        vector<Enode *> vec = elist_to_vector(body->getCdr());
        prune_disjunction(cs, vec, p);
        return;
    } else if (body->isAnd()) {
        vector<Enode *> vec = elist_to_vector(body->getCdr());
        prune_conjunction(cs, vec, p);
        return;
    } else if (body->isNot()) {
        prune_tree(cs, body->get1st(), !p);
        return;
    } else {
        prune_leaf(cs, body, p);
        return;
    }
}

vector<Enode *> contractor_forall::elist_to_vector(Enode * e) const {
    vector<Enode *> vec;
    while (!e->isEnil()) {
        vec.push_back(e->getCar());
        e = e->getCdr();
    }
    return vec;
}

#ifdef USE_NLOPT
double nlopt_eval_enode(const double * x, void * extra) {
    auto extra_info = static_cast<tuple<Enode *, box const &, bool> *>(extra);
    Enode * e = get<0>(*extra_info);
    box const & b = get<1>(*extra_info);
    bool const polarity = get<2>(*extra_info);
    unordered_map<Enode *, double> var_map;
    int i = 0;
    for (Enode * e : b.get_vars()) {
        if (e->isForallVar()) {
            var_map.emplace(e, x[i]);
            i++;
        } else {
            var_map.emplace(e, b[e].mid());
        }
    }
    try {
        double const ret1 = eval_enode(e->get1st(), var_map);
        double const ret2 = eval_enode(e->get2nd(), var_map);
        double ret = 0;
        if (e->isLt() || e->isLeq() || e->isEq()) {
            ret = ret1 - ret2;
        } else if (e->isGt() || e->isGeq()) {
            ret = ret2 - ret1;
        } else if (e->isEq()) {
            throw runtime_error("nlopt_obj: something is wrong.");
        }
        if (!polarity) {
            ret = -ret;
        }
        return ret;
    } catch (exception & e) {
        DREAL_LOG_FATAL << "Exception in nlopt_eval_enode: " << e.what() << endl;
        throw e;
    }
}

void nlopt_fill_gradient(const double * x, double * grad, void * extra) {
    auto extra_info = static_cast<tuple<Enode *, box const &, bool> *>(extra);
    Enode * e = get<0>(*extra_info);
    box const & b = get<1>(*extra_info);
    bool const polarity = get<2>(*extra_info);
    unordered_map<Enode *, double> var_map;
    int i = 0;
    vector<Enode *> forall_var_vec;
    for (Enode * e : b.get_vars()) {
        if (e->isForallVar()) {
            var_map.emplace(e, x[i]);
            i++;
            forall_var_vec.push_back(e);
        } else {
            var_map.emplace(e, b[e].mid());
        }
    }
    i = 0;
    for (Enode * var : forall_var_vec) {
        double deriv_i =
            deriv_enode(e->get1st(), var, var_map) - deriv_enode(e->get2nd(), var, var_map);
        if (e->isGt() || e->isGeq()) {
            deriv_i = -deriv_i;
        }
        if (!polarity) {
            deriv_i = -deriv_i;
        }
        grad[i] = deriv_i;
        i++;
    }
}

double nlopt_obj(unsigned, const double * x, double * grad, void * extra) {
    double const ret = nlopt_eval_enode(x, extra);
    if (grad) {
        nlopt_fill_gradient(x, grad, extra);
    }
    return ret;
}

double nlopt_side_condition(unsigned, const double * x, double * grad, void * extra) {
    double const ret = nlopt_eval_enode(x, extra);
    if (grad) {
        nlopt_fill_gradient(x, grad, extra);
    }
    return ret;
}

box refine_CE_with_nlopt_core(box counterexample, vector<Enode *> const & opt_ctrs,
                              vector<Enode *> const & side_ctrs) {
    // Plug-in `a` into the constraint and optimize `b` in the counterexample `M` by solving:
    //
    //    ∃ y_opt ∈ I_y. ∀ y ∈ I_y. f(a, y_opt) >= f(a, y) — (2)
    //
    // using local optimizer (i.e. nlopt).
    // Let `M’ = (a, b_opt)` be a model for (2).

    DREAL_LOG_DEBUG << "================================" << endl;
    DREAL_LOG_DEBUG << "  Before Refinement              " << endl;
    DREAL_LOG_DEBUG << "================================" << endl;
    DREAL_LOG_DEBUG << counterexample << endl;
    DREAL_LOG_DEBUG << "================================" << endl;
    static bool initialized = false;
    static vector<double> lb, ub, init;
    init.clear();
    for (Enode * e : counterexample.get_vars()) {
        if (e->isForallVar()) {
            if (!initialized) {
                lb.push_back(e->getDomainLowerBound());
                ub.push_back(e->getDomainUpperBound());
            }
            init.push_back(counterexample[e].mid());
            DREAL_LOG_DEBUG << lb.back() << " <= " << init.back() << " <= " << ub.back() << endl;
        }
    }
    size_t const n = init.size();
    static nlopt::opt opt(nlopt::LD_SLSQP, n);
    if (!initialized) {
        opt.set_lower_bounds(lb);
        opt.set_upper_bounds(ub);
        // set tollerance
        // TODO(soonhok): set precision
        // opt.set_xtol_rel(0.0001);
        opt.set_xtol_abs(0.001);
        opt.set_maxtime(0.01);
        initialized = true;
    }

    opt.remove_equality_constraints();
    opt.remove_inequality_constraints();

    // set objective function
    vector<tuple<Enode *, box const &, bool> *> extra_vec;
    Enode * e = opt_ctrs[0];
    bool polarity = false;
    while (e->isNot()) {
        e = e->get1st();
        polarity = !polarity;
    }
    auto extra = new tuple<Enode *, box const &, bool>(e, counterexample, polarity);
    extra_vec.push_back(extra);
    opt.set_min_objective(nlopt_obj, extra);
    opt.add_inequality_constraint(nlopt_side_condition, extra);
    DREAL_LOG_DEBUG << "objective function is added: " << e << endl;

    // set side conditions
    for (Enode * e : side_ctrs) {
        bool polarity = false;
        while (e->isNot()) {
            e = e->get1st();
            polarity = !polarity;
        }
        auto extra = new tuple<Enode *, box const &, bool>(e, counterexample, polarity);
        extra_vec.push_back(extra);
        DREAL_LOG_DEBUG << "refine_counterexample_with_nlopt: Side condition is added: " << e
                        << endl;
        if (e->isEq()) {
            opt.add_equality_constraint(nlopt_side_condition, extra);
        } else if (e->isLt() || e->isLeq() || e->isGt() || e->isGeq()) {
            opt.add_inequality_constraint(nlopt_side_condition, extra);
        }
    }
    try {
        vector<double> output = opt.optimize(init);
        int i = 0;
        for (Enode * e : counterexample.get_vars()) {
            if (e->isForallVar()) {
                counterexample[e] = output[i];
                i++;
            }
        }
    } catch (nlopt::roundoff_limited & e) {
    } catch (std::runtime_error & e) {
        DREAL_LOG_DEBUG << e.what() << endl;
    }

    for (auto extra : extra_vec) {
        delete extra;
    }
    DREAL_LOG_DEBUG << "================================" << endl;
    DREAL_LOG_DEBUG << "  After Refinement              " << endl;
    DREAL_LOG_DEBUG << "================================" << endl;
    DREAL_LOG_DEBUG << counterexample << endl;
    DREAL_LOG_DEBUG << "================================" << endl;
    return counterexample;
}

box refine_CE_with_nlopt(box const & b, vector<Enode *> const & vec) {
    vector<Enode *> opt_ctrs;
    vector<Enode *> side_ctrs;
    for (Enode * e : vec) {
        if (!e->get_exist_vars().empty()) {
            opt_ctrs.push_back(e);
        } else if (!e->get_forall_vars().empty()) {
            side_ctrs.push_back(e);
        }
    }
    if (opt_ctrs.size() != 1) {
        return b;
    }
    box refined_counterexample = refine_CE_with_nlopt_core(b, opt_ctrs, side_ctrs);
    if (refined_counterexample.is_subset(b)) {
        return b;
    } else {
        return refined_counterexample;
    }
}
#endif

contractor make_contractor(Enode * e, lbool const polarity, box const & b,
                           unordered_set<Enode *> const & var_set,
                           scoped_vec<shared_ptr<constraint>> & ctrs) {
    if (e->isNot()) {
        return make_contractor(e->get1st(), !polarity, b, var_set, ctrs);
    }
    if (e->isOr()) {
        // TODO(soonhok): arbitrary number of args
        assert(e->getArity() == 2);
        contractor c1 = make_contractor(e->get1st(), polarity, b, var_set, ctrs);
        contractor c2 = make_contractor(e->get2nd(), polarity, b, var_set, ctrs);
        return mk_contractor_join(c1, c2);
    }
    if (e->isAnd()) {
        vector<contractor> ctcs;
        e = e->getCdr();
        while (!e->isEnil()) {
            ctcs.push_back(make_contractor(e->getCar(), polarity, b, var_set, ctrs));
            e = e->getCdr();
        }
        return mk_contractor_seq(ctcs);
    } else {
        shared_ptr<nonlinear_constraint> nc_ptr =
            make_shared<nonlinear_constraint>(e, var_set, polarity);
        ctrs.push_back(nc_ptr);
        return mk_contractor_ibex_fwdbwd(nc_ptr);
    }
}

box contractor_forall::find_CE_via_underapprox(box const & b,
                                               unordered_set<Enode *> const & forall_vars,
                                               vector<Enode *> const & vec, bool const p,
                                               SMTConfig & config, Egraph & eg) {
    box counterexample(b, forall_vars);
    auto vars = counterexample.get_vars();
    unordered_set<Enode *> const var_set(vars.begin(), vars.end());
    ibex::IntervalVector & iv = counterexample.get_values();
    for (Enode * e : vec) {
        lbool polarity = p ? l_False : l_True;
        if (e->isNot()) {
            e = e->get1st();
            polarity = !polarity;
        }
        if (e->isOr() || e->isAnd()) {
            break;
        }
        Enode * const strengthened_node =
            strengthen_enode(eg, e, config.nra_precision, polarity == l_True);
        nonlinear_constraint ctr(strengthened_node, var_set, l_True);
        if (ctr.is_neq()) {
            break;
        }
        auto numctr = ctr.get_numctr();
        // Construct iv from box b
        ibex::IntervalVector const iv_copy = iv;
        if (numctr->op == ibex::CmpOp::GT || numctr->op == ibex::CmpOp::GEQ) {
            numctr->f.ibwd(ibex::Interval(0.0, POS_INFINITY), iv);
        } else if (numctr->op == ibex::CmpOp::LT || numctr->op == ibex::CmpOp::LEQ) {
            numctr->f.ibwd(ibex::Interval(NEG_INFINITY, 0.0), iv);
        } else if (numctr->op == ibex::CmpOp::EQ) {
            numctr->f.ibwd(ibex::Interval(0.0, 0.0), iv);
        } else {
            ostringstream ss;
            ss << "find_CE_via_underapprox: unknown constraint type, " << *numctr;
            throw runtime_error(ss.str());
        }
        iv &= iv_copy;
        if (iv.is_empty()) {
            // stop when counterexample is already empty;
            return counterexample;
        }
    }
    if (!iv.is_empty()) {
        iv = iv.mid();
    }
    return counterexample;
}

box contractor_forall::find_CE_via_overapprox(box const & b,
                                              unordered_set<Enode *> const & forall_vars,
                                              vector<Enode *> const & vec, bool const p,
                                              SMTConfig & config, Egraph & eg) {
    vector<contractor> ctcs;
    box counterexample(b, forall_vars);
    auto vars = counterexample.get_vars();
    unordered_set<Enode *> var_set(vars.begin(), vars.end());
    scoped_vec<shared_ptr<constraint>> ctrs;
    for (Enode * e : vec) {
        lbool polarity = p ? l_False : l_True;
        if (e->isNot()) {
            polarity = !polarity;
            e = e->get1st();
        }
        Enode * const strengthened_node =
            strengthen_enode(eg, e, config.nra_precision, polarity == l_True);
        contractor ctc = make_contractor(strengthened_node, l_True, counterexample, var_set, ctrs);
        ctcs.push_back(ctc);
    }
    DREAL_THREAD_LOCAL static default_strategy stg;
    contractor ctc = stg.build_contractor(counterexample, ctrs, true, config);
    contractor_status cs(counterexample, config, eg);
    bool const old_delta_test = cs.m_config.nra_delta_test;
    double const old_prec = cs.m_config.nra_precision;
    cs.m_config.nra_delta_test = true;
    cs.m_config.nra_precision = old_prec / 2;
    mcss_icp::solve(ctc, cs, ctrs);
    cs.m_config.nra_delta_test = old_delta_test;
    cs.m_config.nra_precision = old_prec;
    return cs.m_box;
}

box contractor_forall::find_CE(box const & b, unordered_set<Enode *> const & forall_vars,
                               vector<Enode *> const & vec, bool const p, SMTConfig & config,
                               Egraph & eg) {
    // First try to find a counterexample using under-approximation
    box counterexample = find_CE_via_underapprox(b, forall_vars, vec, p, config, eg);
    if (counterexample.is_empty()) {
        // If it fails, try over-approximation method
        counterexample = find_CE_via_overapprox(b, forall_vars, vec, p, config, eg);
    }
#ifdef USE_NLOPT
    // Use local-optimization to improve the quality of CE it fails, try over-approximation method
    if (!counterexample.is_empty() && config.nra_local_opt) {
        return refine_CE_with_nlopt(counterexample, vec);
    }
#endif
    return counterexample;
}

void contractor_forall::prune_disjunction(contractor_status & cs, vector<Enode *> const & vec,
                                          bool const p) {
    DREAL_LOG_DEBUG << "contractor_forall::prune_disjunction" << endl;
    unordered_set<Enode *> forall_vars;
    for (Enode * e : vec) {
        std::unordered_set<Enode *> const & vars = e->get_forall_vars();
        forall_vars.insert(vars.begin(), vars.end());
    }

    unordered_map<Enode *, ibex::Interval> subst;
    if (!forall_vars.empty()) {
        // Step 2. Find a counter-example
        //         Solve(¬ l_1 ∧ ¬ l_2 ∧ ... ∧ ¬ l_n)
        //
        //         Make each ¬ l_i as a contractor ctc_i
        //         Make a fixed_point contractor with ctc_is.
        //         Pass it to icp::solve

        box counterexample = find_CE(cs.m_box, forall_vars, vec, p, cs.m_config, cs.m_egraph);
        if (counterexample.is_empty()) {
            // Step 2.1. (NO Counterexample)
            //           Return B.
            DREAL_LOG_DEBUG << "prune_disjunction: no counterexample found." << endl
                            << "current box = " << endl
                            << cs.m_box << endl;
            cs.m_config.nra_stat.increase_CE();
            return;
        } else {
            // Step 2.2. (There IS a counterexample C)
            //
            //      Using C, prune B.
            //
            // We've found a counterexample (c1, c2) where ¬ f(c1, c2) holds
            // Prune X using a point 'y = c2'. (technically, a point in c2, which is an interval)
            DREAL_LOG_DEBUG << "prune_disjunction: counterexample found.";
            DREAL_LOG_DEBUG << counterexample;
            subst = make_subst_from_value(counterexample, forall_vars);
        }
    }

    // Step 3. Compute B_i = prune(B, l_i)
    //         Update B with ∨ B_i
    //                       i
    auto vars = cs.m_box.get_vars();
    unordered_set<Enode *> const var_set(vars.begin(), vars.end());
    for (Enode * e : vec) {
        if (!e->get_exist_vars().empty()) {
            lbool polarity = p ? l_True : l_False;
            if (e->isNot()) {
                polarity = !polarity;
                e = e->get1st();
            }
            auto ctr = make_shared<nonlinear_constraint>(e, var_set, polarity, subst);
            if (ctr->get_var_array().size() == 0) {
                auto result = ctr->eval(cs.m_box);
                if (result.first != false) {
                    cs.m_box_stack.emplace_back(cs.m_box);
                }
            } else {
                contractor ctc = mk_contractor_ibex_fwdbwd(ctr);
                contractor_status bt(cs, cs.m_box);
                ctc.prune(bt);
                cs.m_output.union_with(bt.m_output);
                unordered_set<shared_ptr<constraint>> const & used_ctrs = bt.m_used_constraints;
                cs.m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
                if (!bt.m_box.is_empty()) {
                    cs.m_box_stack.emplace_back(bt.m_box);
                }
            }
        } else {
            DREAL_LOG_DEBUG << "no exist variable: " << e;
        }
    }
    if (cs.m_box_stack.size() > 0) {
        cs.m_box = cs.m_box_stack.back();
        cs.m_box_stack.pop_back();
    } else {
        cs.m_box.set_empty();
        return;
    }
}

void contractor_forall::prune_conjunction(contractor_status & cs, vector<Enode *> const & vec,
                                          bool const p) {
    DREAL_LOG_DEBUG << "contractor_forall::prune_conjunction" << endl;
    for (Enode * e : vec) {
        DREAL_LOG_DEBUG << "process conjunction element : " << e << endl;
        prune_tree(cs, e, p);
        if (cs.m_box.is_empty()) {
            return;
        }
    }
    return;
}
void contractor_forall::prune_leaf(contractor_status & cs, Enode * body, bool const p) {
    vector<Enode *> vec;
    vec.push_back(body);
    prune_disjunction(cs, vec, p);
    return;
}

void contractor_forall::prune(contractor_status & cs) {
    DREAL_LOG_DEBUG << "contractor_forall prune: " << *m_ctr << endl;
    Enode * const body = m_ctr->get_body();
    DREAL_LOG_DEBUG << "body = " << body << endl;
    prune_tree(cs, body, true);
    return;
}

ostream & contractor_forall::display(ostream & out) const {
    out << "contractor_forall(" << *m_ctr << ")";
    return out;
}

contractor mk_contractor_forall(box const & b, shared_ptr<forall_constraint> const ctr) {
    return contractor(make_shared<contractor_forall>(b, ctr));
}

}  // namespace dreal
