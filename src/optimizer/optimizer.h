/*********************************************************************
Author: Sicun Gao <sicung@cs.cmu.edu>

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
#include <vector>

#include "opensmt/egraph/Egraph.h"
#include "util/box.h"

class Egraph;
class Enode;
struct SMTConfig;

namespace dreal {
class box;

class optimizer {
public:
    optimizer(box &, std::vector<Enode *> const &, Egraph &, SMTConfig &);
    ~optimizer();
    bool improve(box &);
    void set_domain(box &);

private:
    std::vector<Enode *> error_funcs;
    std::unordered_map<Enode *, Enode *> plainf;  // simpler version for differentiation
    box & domain;
    Egraph & egraph;
    SMTConfig & config;
    std::vector<box *> point_trace;  // all points that have been moved around by the optimizer
    std::vector<box *> holes;        // empty spaces found duing the optimization
    bool prioritize_me;              // this is set to true when optimizer finds a highly likely box
    std::vector<Enode *> learned;    // learned clauses
private:
    bool improve_naive(box &);
    void learn(std::vector<Enode *> &);  // add learned clauses to an external storage
};
}  // namespace dreal
