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

#include <cstring>
#include <functional>
#include "ibex/ibex.h"

namespace std {
template<>
struct hash<ibex::Variable> {
    size_t operator () (const ibex::Variable & v) const {
        int h = 0;
        char const * str = v.symbol->name;
        while (*str)
            h = h << 1 ^ *str++;
        return h;
    }
};
template<>
struct equal_to<ibex::Variable> {
    bool operator() (const ibex::Variable & v1, const ibex::Variable & v2) const {
        return strcmp(v1.symbol->name, v2.symbol->name) == 0;
    }
};
}  // namespace std
