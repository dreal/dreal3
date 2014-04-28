/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <iostream>
#include "realpaver/rp_interval.h"
namespace dreal {
class interval {
public:
    double lb;
    double ub;
    interval();
    interval(double const l, double const u);
    interval(rp_interval const rp_intv);
    std::ostream & print(std::ostream & out, unsigned digits = 16, bool exact = false) const;
    friend std::ostream & operator<<(std::ostream & out, interval const & i);
};

std::ostream & operator<<(std::ostream & out, interval const & i);
}
