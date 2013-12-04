/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <string>
#include <sstream>

bool starts_with(std::string const & s, std::string const & prefix);
bool ends_with(std::string const & s, std::string const & ending);
template<typename T>
std::string join(T const & container, std::string const & sep) {
    auto it = begin(container);
    auto end_it = end(container);
    std::stringstream ss;
    ss << *(it++);
    for (; it != end_it; it++) {
        ss << sep << *it;
    }
    return ss.str();
}
