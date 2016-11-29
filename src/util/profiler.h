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
#include <chrono>
#include <ostream>
#include <string>

namespace dreal {
class profiler {
    std::string m_name;
    std::ostream & m_out;
    std::chrono::high_resolution_clock::time_point m_begin;

    profiler(std::string const & n, std::ostream & out)
        : m_name(n), m_out(out), m_begin(std::chrono::high_resolution_clock::now()) {}
    ~profiler() {
        using dura = std::chrono::duration<double>;
        auto d = std::chrono::high_resolution_clock::now() - m_begin;
        m_out << m_name << ": " << std::chrono::duration_cast<dura>(d).count() << std::endl;
    }
};

#define DREAL_PROFILE_BLOCK(name, out) profiler _pfinstance(name, out)
}  // namespace dreal
