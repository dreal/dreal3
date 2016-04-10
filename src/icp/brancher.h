#pragma once

#include <vector>
#include <memory>
#include "util/scoped_vec.h"
#include "util/box.h"
#include "contractor/contractor.h"
using std::shared_ptr;
using std::vector;

namespace dreal {
    class BranchHeuristic {
        public:
            vector<int> sort_branches(box const &, double) const;
            virtual vector<double> score_axes(box const & b) const =0;
    };

    class SizeBrancher: public BranchHeuristic {
        public:
            vector<double> score_axes(box const & b) const ;
    };

    class SizeGradAsinhBrancher: public BranchHeuristic {
        public:
            SizeGradAsinhBrancher(scoped_vec<shared_ptr<constraint>>& constraints, double c1 = 1000, double c2 = 1000, double c3 = 0.01) :
               constraints(constraints), c1(c1), c2(c2), c3(c3) {};
            vector<double> score_axes(box const & b) const;
        private:
            const scoped_vec<shared_ptr<constraint>> constraints;
            const double c1;
            const double c2;
            const double c3;
    };
}
