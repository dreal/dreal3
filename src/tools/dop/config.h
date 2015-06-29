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

#pragma once
#include <pegtl.hh>
#include <cassert>
#include <iostream>
#include <string>
#include <vector>
#include <unordered_map>
#include "opensmt/egraph/Enode.h"
#include "ezOptionParser/ezOptionParser.hpp"

namespace dop {

class config {
private:
    std::string m_filename;
    unsigned long m_viz_gridsize = 50;
    bool m_read_from_stdin = false;
    void printUsage(ez::ezOptionParser & opt);
    void init(std::string const & filename, unsigned long const viz_gridsize, bool const read_from_stdin) {
        m_filename = filename;
        m_viz_gridsize = viz_gridsize;
        m_read_from_stdin = read_from_stdin;
    }

public:
    config(int const argc, const char * argv[]);
    std::string get_filename() { return m_filename; }
    unsigned long get_viz_gridsize() { return m_viz_gridsize; }
    bool get_read_from_stdin() { return m_read_from_stdin; }
};

}  // namespace dop
