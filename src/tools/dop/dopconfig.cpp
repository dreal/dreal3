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
#include <sys/stat.h>
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
    opt.add("", false, 0, 0,
            "use local optimization to refine counterexamples",
            "--local-opt");
    opt.add("", false, 0, 0,
            "show debug information",
            "--debug");
    opt.add("", false, 0, 0,
            "use polytope contractor",
            "--polytope");
    opt.add("", false, 0, 0,
            "NO sync the domains of forall variables using corresponding existential variables",
            "--no-sync");
    opt.add("", false, 0, 0,
            "print out statistics",
            "--stat");
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
    if (opt.isSet("--run-visualization")) { set_run_visualization(true); }
    if (opt.isSet("--save-visualization")) { set_save_visualization(true); }
    if (opt.isSet("--vis-cell")) {
        unsigned long vis_cell = 0.0;
        opt.get("--vis-cell")->getULong(vis_cell);
        set_vis_cell(vis_cell);
    }
    if (opt.isSet("--local-opt")) { set_local_opt(true); }
    if (opt.isSet("--debug")) { set_debug(true); }
    if (opt.isSet("--polytope")) { set_polytope(true); }
    if (opt.isSet("--no-sync")) { set_sync(false); }
    if (opt.isSet("--stat")) { set_stat(true); }

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
        size_t pos_of_dot_in_filename = filename.find_last_of(".");
        if (pos_of_dot_in_filename == string::npos) {
            cerr << "filename: " << filename
                 << " does not have an extension.";
            exit(1);
        }
        string const file_ext = filename.substr(pos_of_dot_in_filename + 1);
        if (file_ext == "dop") {
            set_type(type::DOP);
        } else if (file_ext == "bar") {
            set_type(type::BARON);
        } else if (file_ext == "bch") {
            set_type(type::BCH);
        } else {
            cerr << "Input file: " << filename << endl
                 << "Note: we only support .dop and .bar files." << endl;
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
