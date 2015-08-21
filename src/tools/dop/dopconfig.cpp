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

#include "tools/dop/dopconfig.h"
#include <pegtl.hh>
#include <cassert>
#include <algorithm>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

namespace dop {

using std::cerr;
using std::cout;
using std::endl;
using std::ostream;
using std::string;
using std::vector;

void config::printUsage(ez::ezOptionParser & opt) {
        string usage;
        opt.getUsage(usage, 160);
        cout << usage;
        exit(1);
}

config::config(int const argc, const char * argv[]) {
    ez::ezOptionParser opt;
    opt.add("", false, 0, 0,
            "Display usage instructions.",
            "-h", "-help", "--help", "--usage");
    opt.add("", false, 0, 0,
            "visualize the result",
            "--run-visualization", "--run-vis");
    opt.add("", false, 0, 0,
            "save Python visualization code",
            "--save-visualization", "--save-vis");
    opt.add("", false, 1, 0,
            "[visualization] # of cells in one dimension",
            "--vis-cell");
    opt.add("", false, 1, 0,
            "set precision (default 0.001)\n"
            "this overrides the value specified in input files",
            "--precision");
    opt.parse(argc, argv);
    opt.overview  = "dOp ";

    // Usage Information
    opt.overview += " : delta-complete Optimizer";
    opt.syntax    = "dOp [OPTIONS] <input file>";
    if (opt.isSet("-h")) {
        printUsage(opt);
    }

    // precision
    if (opt.isSet("--precision")) {
        double prec = 0.0;
        opt.get("--precision")->getDouble(prec);
        set_precision(prec);
    }

    // visualization options
    if (opt.isSet("--run-visualization")) {
        set_run_visualization(true);
    }
    if (opt.isSet("--save-visualization")) {
        set_save_visualization(true);
    }
    if (opt.isSet("--vis-cell")) {
        unsigned long vis_cell = 0.0;
        opt.get("--vis-cell")->getULong(vis_cell);
        set_vis_cell(vis_cell);
    }



    // Set up filename
    string filename;
    vector<string*> args;
    copy(opt.firstArgs.begin() + 1, opt.firstArgs.end(),   back_inserter(args));
    copy(opt.unknownArgs.begin(),   opt.unknownArgs.end(), back_inserter(args));
    copy(opt.lastArgs.begin(),      opt.lastArgs.end(),    back_inserter(args));
    if (args.size() != 1) {
        printUsage(opt);
    }
    filename = *args[0];
    if (filename.length() > 0) {
        struct stat s;
        if (stat(filename.c_str(), &s) != 0 || !(s.st_mode & S_IFREG)) {
            cerr << "can't open file:" << filename << endl;
            exit(1);
        }
    }
    set_filename(filename);
}

ostream & operator<<(ostream & out, config const & c) {
    out << "filename           = " << c.m_filename << endl;
    out << "vis_cell           = " << c.m_vis_cell << endl;
    out << "run visualization  = " << c.m_run_visualization << endl;
    out << "save visualization = " << c.m_save_visualization << endl;
    out << "precision          = " << c.m_prec;
    return out;
}

}  // namespace dop
