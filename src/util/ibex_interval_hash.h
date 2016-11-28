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

#pragma once
#include <cstring>
#include <functional>
#include <vector>
#include "ibex/ibex.h"
#include "util/hash_combine.h"

namespace std {
template <>
struct hash<ibex::Interval> {
    size_t operator()(const ibex::Interval & v) const {
        size_t seed = 23;
        dreal::hash_combine<double>(seed, v.lb());
        dreal::hash_combine<double>(seed, v.ub());
        return seed;
    }
};
template <>
struct equal_to<ibex::Interval> {
    bool operator()(const ibex::Interval & v1, const ibex::Interval & v2) const {
        return v1.lb() == v2.lb() && v1.ub() == v2.ub();
    }
};

template <>
struct hash<std::vector<ibex::Interval>> {
    size_t operator()(const std::vector<ibex::Interval> & v) const {
        size_t seed = 23;
        for (ibex::Interval const & iv : v) {
            dreal::hash_combine<ibex::Interval>(seed, iv);
        }
        return seed;
    }
};
template <>
struct equal_to<std::vector<ibex::Interval>> {
    bool operator()(const std::vector<ibex::Interval> & v1,
                    const std::vector<ibex::Interval> & v2) const {
        if (v1.size() != v2.size()) {
            return false;
        }
        for (unsigned i = 0; i < v1.size(); i++) {
            if (v1[i] != v2[i]) {
                return false;
            }
        }
        return true;
    }
};

}  // namespace std
