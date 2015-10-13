/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include <sys/stat.h>
#include <ezOptionParser/ezOptionParser.hpp>
#include <algorithm>
#include <cassert>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iostream>
#include <limits>
#include <list>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include "./config.h"
#include "./version.h"
#include "opensmt/api/OpenSMTContext.h"
#include "opensmt/egraph/Enode.h"
#include "tools/dop/dopconfig.h"
#include "util/subst_enode.h"
#include "tools/dop/print_latex.h"
#include "tools/dop/print_py.h"
#include "tools/dop/process.h"
#include "tools/dop/visualize.h"
#include "util/logging.h"
#include "util/string.h"

using std::back_inserter;
using std::cerr;
using std::cout;
using std::copy;
using std::endl;
using std::list;
using std::numeric_limits;
using std::ofstream;
using std::pair;
using std::runtime_error;
using std::sort;
using std::string;
using std::unordered_map;
using std::vector;
using std::stringstream;
using std::ostream;


// Dop Parser
extern int dopset_in(FILE * fin);
extern int dopparse();
extern int doplex_destroy();
extern void dop_init_parser();
extern void dop_cleanup_parser();
extern OpenSMTContext * dop_ctx;
extern bool dop_minimize;
extern double dop_prec;
extern vector<Enode *> dop_ctrs;
extern vector<Enode *> dop_costs;
extern unordered_map<string, Enode*> dop_var_map;

// Baron Parser
extern int baronset_in(FILE * fin);
extern int baronparse();
extern int baronlex_destroy();
extern void baron_init_parser();
extern void baron_cleanup_parser();
extern OpenSMTContext * baron_ctx;
extern bool baron_minimize;
extern vector<Enode*> baron_ctrs;
extern Enode * baron_cost_fn;
extern unordered_map<string, Enode*> baron_var_map;

// BCH Parser
extern int bchset_in(FILE * fin);
extern int bchparse();
extern int bchlex_destroy();
extern void bch_init_parser();
extern void bch_cleanup_parser();
extern OpenSMTContext * bch_ctx;
extern bool bch_minimize;
extern vector<Enode*> bch_ctrs;
extern vector<Enode *> bch_costs;
extern unordered_map<string, Enode*> bch_var_map;

namespace dop {

static const char g_minimum_name[] = "min";

Enode * subst_exist_vars_to_univerally_quantified(OpenSMTContext & ctx, unordered_map<string, Enode *> const & m, Enode * f) {
    // Input:  f(x1, ..., xn) where xi is existentially quantified var.
    // Output: f(y1, ..., yn) where yi is universally quantified var.
    unordered_map<Enode *, Enode *> subst_map;
    // 1. need to create a mapping from exist variables to forall variables
    Snode * const real_sort = ctx.mkSortReal();
    for (auto const & p : m) {
        string const name = p.first;
        string const forall_var_name = string("forall_") + name;
        Enode * exist_var = p.second;
        double const lb = exist_var->getDomainLowerBound();
        double const ub = exist_var->getDomainUpperBound();
        ctx.DeclareFun(forall_var_name.c_str(), real_sort);
        Enode * const forall_var = ctx.mkVar(forall_var_name.c_str(), true);
        forall_var->setForallVar();
        forall_var->setDomainLowerBound(lb);
        forall_var->setDomainUpperBound(ub);
        forall_var->setValueLowerBound(lb);
        forall_var->setValueUpperBound(ub);
        subst_map.emplace(exist_var, forall_var);
    }
    // 2. need to make f(y1, y2) based on f(x1, x2)
    Enode * forall_f = dreal::subst(ctx, f, subst_map);
    return forall_f;
}

Enode * make_leq_cost(OpenSMTContext & ctx, unordered_map<string, Enode *> const & m, Enode * f, Enode * min_var) {
    // Input:  f(x1, ..., xn)        where xi is existentially quantified var.
    // Output: min <= f(y1, ..., yn) where yi is universally quantified var.
    Enode * forall_f = subst_exist_vars_to_univerally_quantified(ctx, m, f);
    Enode * const args_list = ctx.mkCons(min_var, ctx.mkCons(forall_f));
    Enode * const leq = ctx.mkLeq(args_list);
    return leq;
}

Enode * make_min_var(OpenSMTContext & ctx, unordered_map<string, Enode *> & m, unsigned int i) {
    stringstream ss;
    Snode * const real_sort = ctx.mkSortReal();
    ss << g_minimum_name << "_" << i;
    string name = ss.str();
    ctx.DeclareFun(name.c_str(), real_sort);
    Enode * const min_var = ctx.mkVar(name.c_str(), true);
    min_var->setDomainLowerBound(numeric_limits<double>::lowest());
    min_var->setDomainUpperBound(numeric_limits<double>::max());
    m.emplace(name, min_var);
    return min_var;
}

Enode * make_eq_cost(OpenSMTContext & ctx, Enode * e1, Enode * e2) {
    Enode * const eq = ctx.mkEq(ctx.mkCons(e1, ctx.mkCons(e2)));
    return eq;
}

ostream & display(ostream & out, string const & name, Enode * const e) {
    out << name << " = "
        << "[" << e->getValueLowerBound() << ", "
        << e->getValueUpperBound() << "]";
    return out;
}

void print_result(unordered_map<string, Enode*> const & map) {
    vector<pair<string, Enode*>> vec;
    vec.insert(vec.end(), map.begin(), map.end());
    sort(vec.begin(), vec.end(), [](pair<string, Enode *> const & p1, pair<string, Enode *> const & p2) {
            bool const p1_starts_with_min = dreal::starts_with(p1.first, g_minimum_name);
            bool const p2_starts_with_min = dreal::starts_with(p2.first, g_minimum_name);
            if (p1_starts_with_min && !p2_starts_with_min) {
                return false;
            }
            if (!p1_starts_with_min && p2_starts_with_min) {
                return true;
            }
            return p1.first < p2.first;
        });
    for (auto const item : vec) {
        string name = item.first;
        Enode * e = item.second;
        cout << "\t"; dop::display(cout, name, e) << endl;
    }
}

Enode * make_vec_to_list(OpenSMTContext & ctx, vector<Enode *> v) {
    list<Enode*> args(v.begin(), v.end());
    return ctx.mkCons(args);
}

int process_main(OpenSMTContext & ctx, config const & config, vector<Enode *> const & costs, unordered_map<string, Enode*> var_map, vector<Enode *> const & ctrs_X);

int process_baron(config const & config) {
    FILE * fin = nullptr;
    string filename = config.get_filename();
    // Make sure file exists
    if ((fin = fopen(filename.c_str(), "rt")) == nullptr) {
        opensmt_error2("can't open file", filename.c_str());
    }
    ::baronset_in(fin);
    ::baron_init_parser();
    ::baronparse();
    OpenSMTContext & ctx = *baron_ctx;
    if (config.get_precision() > 0) {
        ctx.setPrecision(config.get_precision());
    }
    ctx.setLocalOpt(config.get_local_opt());
    ctx.setDebug(config.get_debug());
    ctx.setPolytope(config.get_polytope());
    ctx.setShrinkForDop(config.get_sync());
    unordered_map<string, Enode *> var_map = baron_var_map;
    Enode * const cost_fn = baron_cost_fn;
    vector<Enode *> & ctrs_X = baron_ctrs;
    int const ret = process_main(ctx, config, {cost_fn}, var_map, ctrs_X);
    ::baronlex_destroy();
    fclose(fin);
    ::baron_cleanup_parser();
    return ret;
}

int process_dop(config const & config) {
    FILE * fin = nullptr;
    string filename = config.get_filename();
    // Make sure file exists
    if ((fin = fopen(filename.c_str(), "rt")) == nullptr) {
        opensmt_error2("can't open file", filename.c_str());
    }
    ::dopset_in(fin);
    ::dop_init_parser();
    ::dopparse();
    OpenSMTContext & ctx = *dop_ctx;
    if (dop_prec > 0) {
        ctx.setPrecision(dop_prec);
    }
    if (config.get_precision() > 0) {
        ctx.setPrecision(config.get_precision());
    }
    ctx.setLocalOpt(config.get_local_opt());
    ctx.setDebug(config.get_debug());
    ctx.setPolytope(config.get_polytope());
    ctx.setShrinkForDop(config.get_sync());
    unordered_map<string, Enode *> var_map = dop_var_map;
    vector<Enode *> & costs = dop_costs;
    vector<Enode *> & ctrs_X = dop_ctrs;
    int const ret = process_main(ctx, config, costs, var_map, ctrs_X);
    ::doplex_destroy();
    fclose(fin);
    ::dop_cleanup_parser();
    return ret;
}

int process_bch(config const & config) {
    FILE * fin = nullptr;
    string filename = config.get_filename();
    // Make sure file exists
    if ((fin = fopen(filename.c_str(), "rt")) == nullptr) {
        opensmt_error2("can't open file", filename.c_str());
    }
    ::bchset_in(fin);
    ::bch_init_parser();
    ::bchparse();
    OpenSMTContext & ctx = *bch_ctx;
    if (config.get_precision() > 0) {
        ctx.setPrecision(config.get_precision());
    }
    ctx.setLocalOpt(config.get_local_opt());
    ctx.setDebug(config.get_debug());
    ctx.setPolytope(config.get_polytope());
    ctx.setShrinkForDop(config.get_sync());
    unordered_map<string, Enode *> var_map = bch_var_map;
    vector<Enode *> & costs = bch_costs;
    vector<Enode *> & ctrs_X = bch_ctrs;
    int const ret = process_main(ctx, config, costs, var_map, ctrs_X);
    ::bchlex_destroy();
    fclose(fin);
    ::bch_cleanup_parser();
    return ret;
}

int process_main(OpenSMTContext & ctx,
                 config const & config,
                 vector<Enode *> const & costs,
                 unordered_map<string, Enode*> var_map,
                 vector<Enode *> const & ctrs_X) {
    // minimize cost_i(x)
    // satisfying ctr_j(x)
    //
    // exists x. ctr(x) /\ forall y. [ctr(y) -> (cost(x) <= cost(y))]
    // exists x. ctr(x) /\ forall y. [!ctr(y) \/ (cost(x) <= cost(y))]
    // exists x, min_1, ..., min_n.
    //              /\ cost_i(x) = min_i
    //               i
    //
    //              /\ ctr_j(x)
    //               j
    //
    //              /\ forall y. [\/ !ctr_j(y) \/ min_i <= cost_i(y))]
    //                             j            i
    vector<Enode *> or_ctrs;
    for (Enode * ctr_X : ctrs_X) {
        Enode * ctr_not_Y = ctx.mkNot(ctx.mkCons(subst_exist_vars_to_univerally_quantified(ctx, var_map, ctr_X)));  // ctr(y)
        or_ctrs.push_back(ctr_not_Y);
    }

    vector<Enode*> eq_costs;
    for (unsigned i = 0; i < costs.size(); ++i) {
        Enode * min_var_i = make_min_var(ctx, var_map, i);                      // min
        Enode * eq_cost  = make_eq_cost(ctx, costs[i], min_var_i);              // cost_i(x) = min_i
        Enode * leq_cost = make_leq_cost(ctx, var_map, costs[i], min_var_i);    // min <= costs[0](y)
        eq_costs.push_back(eq_cost);
        or_ctrs.push_back(leq_cost);
    }

    // !ctr_1(y) \/ ... \/ !ctr_m(y) \/ (min_1 <= costs_1(y) ... \/ (min_n <= costs_n(y)
    Enode * or_term = ctx.mkOr(make_vec_to_list(ctx, or_ctrs));
    vector<pair<string, Snode *>> sorted_var_list;
    for (Enode * e : or_term->get_forall_vars()) {
        pair<string, Snode *> p = make_pair(e->getCar()->getName(), e->getSort());
        sorted_var_list.push_back(p);
    }
    Enode * quantified = ctx.mkForall(sorted_var_list, or_term);
    cout << "Precision  : " << ctx.getPrecision() << endl;
    for (auto var : var_map) {
        cout << "Variable   : " << var.first
             << " in [" << var.second->getDomainLowerBound() << ", "
             << var.second->getDomainUpperBound() << "]" << endl;
    }
    for (Enode * cost : costs) {
        cout << "Minimize   : " << cost << endl;
    }
    for (Enode * ctr_X : ctrs_X) {
        cout << "Constraint : " << ctr_X << endl;
    }
    for (Enode * eq_cost : eq_costs) {
        ctx.Assert(eq_cost);
    }
    for (Enode * ctr_X : ctrs_X) {
        ctx.Assert(ctr_X);
    }
    ctx.Assert(quantified);
    auto result = ctx.CheckSAT();
    cout << "Result     : ";
    if (result == l_True) {
        cout << "delta-sat" << endl;
        print_result(var_map);
        if (config.get_save_visualization()) {
            string vis_filename = config.get_filename() + ".py";
            ofstream of(vis_filename);
            // TODO(soonhok): generalize for a multi-obj case
            save_visualization_code(of, costs[0], var_map, config.get_vis_cell(), "min_0");
            cout << "Visualization Code is saved at " << vis_filename << endl;
        }
        if (config.get_run_visualization()) {
            // TODO(soonhok): generalize for a multi-obj case
            run_visualization(costs[0], var_map, config.get_vis_cell(), "min_0");
        }
    } else {
        cout << "unsat" << endl;
    }
    return 0;
}
}  // namespace dop
