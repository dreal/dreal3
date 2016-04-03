#include <vector>
#include <tuple>
#include <algorithm>
#include <memory>
#include "icp/brancher.h"
#include "util/scoped_vec.h"
#include "util/box.h"
#include "contractor/contractor.h"
using std::vector;
using std::shared_ptr;
using std::tuple;

namespace dreal {

    vector<int> BranchHeuristic::sort_branches(box const & b, scoped_vec<shared_ptr<constraint>> & constraints, double branch_precision) const {
        vector<int> bisectable_dims = b.bisectable_dims(branch_precision);
        vector<int> sorted_dims;
        vector<tuple<double, int>> bisectable_axis_scores;

        vector<double> axis_scores = this->score_axes(b, constraints);
        for (int dim : bisectable_dims) {
            bisectable_axis_scores.push_back(tuple<double, int>(-axis_scores[dim], dim));
        }

        std::sort(bisectable_axis_scores.begin(), bisectable_axis_scores.end());
        for (auto tup : bisectable_axis_scores) {
            sorted_dims.push_back(std::get<1>(tup));
        }
        return sorted_dims;
    }

    vector<double> SizeBrancher::score_axes(box const & b, scoped_vec<shared_ptr<constraint>> &) const {
        const ibex::IntervalVector &values = b.get_values();
        ibex::Vector radii = values.rad();
        ibex::Vector midpt = values.mid();
        vector<double> scores(b.size());
        for (unsigned i = 0; i < b.size(); i++) {
            scores[i] = radii[i];
        }
        return scores;
    }

    vector<double> SizeGradAsinhBrancher::score_axes(box const & b, scoped_vec<shared_ptr<constraint>> & constraints) const {
        const ibex::IntervalVector &values = b.get_values();
        ibex::Vector radii = values.rad();
        ibex::Vector midpt = values.mid();
        vector<double> scores(b.size());

        for (unsigned i = 0; i < b.size(); i++) {
            scores[i] = asinh(radii[i]*this->c1)*this->c3;
        }

        for (auto cptr : constraints) {
            if (cptr->get_type() == constraint_type::Nonlinear) {
                auto ncptr = std::dynamic_pointer_cast<nonlinear_constraint>(cptr);
                (&ncptr->get_numctr()->f)->gradient(midpt, this->gradout);
                ibex::Vector g = this->gradout.lb();
                for (unsigned i = 0; i < b.size(); i++) {
                    scores[i] += asinh(fabs(g[i] * radii[i])*this->c2) / constraints.size();
                }
            }
        }
        return scores;
    }
}
