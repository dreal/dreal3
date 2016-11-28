/*********************************************************************
Author: Calvin Huang <c@lvin.me>
        Soonho Kong  <soonhok@cs.cmu.edu>

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

#include "icp/brancher.h"

#include <assert.h>
#include <math.h>
#include <algorithm>
#include <memory>
#include <stdexcept>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>

#include "constraint/constraint.h"
#include "ibex_Interval.h"
#include "ibex_IntervalVector.h"
#include "ibex_Vector.h"
#include "interval/interval.icc"
#include "minisat/core/SolverTypes.h"
#include "smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/scoped_vec.h"

using std::get;
using std::pair;
using std::shared_ptr;
using std::sort;
using std::tuple;
using std::unordered_set;
using std::runtime_error;
using std::vector;

namespace dreal {

vector<int> BranchHeuristic::sort_branches(box const & b,
                                           scoped_vec<shared_ptr<constraint>> const & ctrs,
                                           ibex::BitSet const & input, SMTConfig const & config,
                                           int num_try) const {
    double branch_precision = config.nra_precision;
    vector<int> sorted_dims;
    if (config.nra_delta_test) {
        // If nra_delta_test is used, either return {} or adjust branch_precision to be zero.
        bool delta_test_passed = true;
        for (shared_ptr<constraint> const & ctr : ctrs) {
            switch (ctr->get_type()) {
                case constraint_type::Nonlinear: {
                    pair<lbool, ibex::Interval> const eval_result = ctr->eval(b);
                    if (eval_result.first == l_True) {
                        continue;
                    }
                    if (eval_result.second.is_bisectable() &&
                        eval_result.second.diam() > branch_precision) {
                        delta_test_passed = false;
                    }
                    break;
                }
                case constraint_type::ODE: {
                    // |X_0|, |X_t|, and |par| has to be < delta
                    for (auto const & var : ctr->get_occured_vars()) {
                        if (b[var].is_bisectable() && b[var].diam() > branch_precision) {
                            delta_test_passed = false;
                            break;
                        }
                    }
                    break;
                }
                case constraint_type::Integral:
                    throw runtime_error(
                        "BranchHeuristic::sort_branches: found Integral constraint");
                case constraint_type::ForallT:
                    break;
                case constraint_type::Exists:
                    throw runtime_error("BranchHeuristic::sort_branches: found Exists constraint");
                case constraint_type::Forall:
                    // TODO(soonhok): set delta_test_passed to be false if a counterexample is
                    // found.
                    throw runtime_error("BranchHeuristic::sort_branches: found Forall constraint");
            }
            if (!delta_test_passed) {
                break;
            }
        }
        if (delta_test_passed) {
            assert(sorted_dims.size() == 0);
            return sorted_dims;
        } else {
            branch_precision = 0.0;
        }
    }
    vector<int> const bisectable_dims = b.bisectable_dims(branch_precision, input);
    vector<double> const axis_scores = score_axes(b);
    vector<tuple<double, int>> bisectable_axis_scores;
    for (int const dim : bisectable_dims) {
        bisectable_axis_scores.push_back(tuple<double, int>(-axis_scores[dim], dim));
    }
    sort(bisectable_axis_scores.begin(), bisectable_axis_scores.end());
    for (auto const & tup : bisectable_axis_scores) {
        sorted_dims.push_back(get<1>(tup));
        if (--num_try <= 0) {
            break;
        }
    }
    return sorted_dims;
}

vector<double> SizeBrancher::score_axes(box const & b) const {
    ibex::Vector const radii = b.get_values().rad();
    vector<double> scores(b.size());
    for (unsigned i = 0; i < b.size(); i++) {
        scores[i] = radii[i];
    }
    return scores;
}

vector<double> SizeGradAsinhBrancher::score_axes(box const & b) const {
    const ibex::IntervalVector & values = b.get_values();
    ibex::Vector radii = values.rad();
    ibex::Vector midpt = values.mid();
    vector<double> scores(b.size());

    for (unsigned i = 0; i < b.size(); i++) {
        scores[i] = asinh(radii[i] * c1) * c3;
    }

    for (auto cptr : constraints) {
        if (cptr->get_type() == constraint_type::Nonlinear) {
            auto gradout = cptr->grad(midpt);
            // TODO(soonhok): when gradout is an empty interval, the
            // following line fails.
            if (!gradout.is_empty()) {
                ibex::Vector g = gradout.lb();
                for (unsigned i = 0; i < b.size(); i++) {
                    scores[i] += asinh(fabs(g[i] * radii[i]) * c2) / constraints.size();
                }
            }
        }
    }
    return scores;
}
}  // namespace dreal
