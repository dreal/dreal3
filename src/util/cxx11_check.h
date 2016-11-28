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
#include <iostream>
#include <type_traits>

#include "util/type_name.h"

namespace dreal {
template <typename T>
bool check_nothrow_move_constructible() {
    bool ret = std::is_nothrow_move_constructible<T>::value;
    std::cerr << type_name<T>() << ":\t"
              << "is_nothrow_move_constructible = " << ret << std::endl;
    return ret;
}

template <typename T>
bool check_move_constructible() {
    bool ret = std::is_move_constructible<T>::value;
    std::cerr << type_name<T>() << ":\t"
              << "is_move_constructible = " << ret << std::endl;
    return ret;
}
}  // namespace dreal
