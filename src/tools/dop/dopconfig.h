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
    unsigned long m_vis_cell = 50.0;
    bool m_run_visualization = false;
    bool m_save_visualization = false;
    double m_prec = 0.0;

    void printUsage(ez::ezOptionParser & opt);
    void set_filename(std::string const & filename) { m_filename = filename; }
    void set_run_visualization(bool const b) { m_run_visualization = b; }
    void set_save_visualization(bool const b) { m_save_visualization = b; }
    void set_vis_cell(unsigned long const vis_cell) { m_vis_cell = vis_cell; }
    void set_precision(double const prec) { m_prec = prec; }

public:
    config(int const argc, const char * argv[]);
    std::string get_filename() { return m_filename; }
    unsigned long get_vis_cell() { return m_vis_cell; }
    bool get_run_visualization() const { return m_run_visualization; }
    bool get_save_visualization() const { return m_save_visualization; }
    double get_precision() const {
        return m_prec;
    }
    friend std::ostream & operator<<(std::ostream & out, config const & c);
};

std::ostream & operator<<(std::ostream & out, config const & c);

}  // namespace dop
