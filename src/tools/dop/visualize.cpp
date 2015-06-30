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

#include <unordered_map>
#include <string>
#include <sstream>
#include "config.h"
#include "version.h"
#include "tools/dop/visualize.h"
#include "opensmt/egraph/Enode.h"
#include "tools/dop/print_py.h"
#include "tools/dop/print_latex.h"

namespace dop {
using std::unordered_map;
using std::string;
using std::stringstream;
using std::cerr;
using std::endl;
using std::to_string;

#ifdef PYTHONLIBS_FOUND
#include "Python.h"
string generate_py_visualization_string(Enode * const f, unordered_map<string, Enode *> var_map, string const & minimum_name) {
    Enode * minimum = var_map[minimum_name];
    var_map.erase(minimum_name);
    stringstream ss;

    // print function
    ss << "def object_function(";
    for (auto const & p : var_map) {
        ss << p.first << ", ";
    }
    ss << "):" << endl
        << "    " << "return ";
    print_py_infix(ss, f);
    ss << endl;

    // print range
    unsigned i = 1;
    for (auto const & p : var_map) {
        ss << "domain_" << to_string(i++) << " = "
            << "[" << p.second->getDomainLowerBound() << ", " << p.second->getDomainUpperBound() << "]"
            << endl;
    }

    // print value
    i = 1;
    for (auto const & p : var_map) {
        ss << "value_" << to_string(i++) << " = "
            << "[" << p.second->getValueLowerBound() << ", " << p.second->getValueUpperBound() << "]"
            << endl;
    }

    // print min
    ss << "minimum = " << "[" << minimum->getValueLowerBound() << ", " << minimum->getValueUpperBound() << "]"
        << endl;

    // print title
    ss << "g_fig.suptitle(r'$";
    print_latex_infix(ss, f);
    ss << "$', fontsize=14, fontweight='bold')" << endl;

    // set axis label
    auto it = var_map.cbegin();
    ss << "g_ax.set_xlabel(\""
        << (it++)->first
        << "\")" << endl;
    ss << "g_ax.set_ylabel(\""
        << it->first
        << "\")" << endl;
    ss << "g_ax.set_zlabel(\"z\")" << endl;
    return ss.str();
}

void visualize_result_via_python(Enode * const f, unordered_map<string, Enode *> const & var_map, string const & minimum_name) {
    static string const python_code_header = R"(
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d import proj3d
from matplotlib import cm
from matplotlib.ticker import LinearLocator, FormatStrFormatter
import pylab
import matplotlib.pyplot as plt
import numpy

global g_labels_and_points, g_ax, g_fig
g_labels_and_points = []
g_fig = plt.figure(facecolor="white")
g_ax = g_fig.gca(projection='3d')

def update_position(e):
    for label, x, y, z in g_labels_and_points:
        x2, y2, _ = proj3d.proj_transform(x, y, z, g_ax.get_proj())
        label.xy = x2,y2
        label.update_positions(g_fig.canvas.renderer)
    g_fig.canvas.draw()

def trisurf_plot(ax, dom_X, dom_Y, f, p, grid = 50.0):
    [x_lb, x_ub] = dom_X
    [y_lb, y_ub] = dom_Y
    grid = float(grid)
    x = numpy.arange(x_lb, x_ub, (x_ub - x_lb) / grid)
    y = numpy.arange(y_lb, y_ub, (y_ub - y_lb) / grid)
    X, Y = numpy.meshgrid(x, y)
    x = X.flatten()
    y = Y.flatten()
    z = f(x, y)
    ax.plot_trisurf(x, y, z, cmap=cm.jet, linewidth=0.2)
    if p:
        [p_x, p_y, p_z] = [ sum(l, 0.0) / len(l) for l in p]
        x2, y2, _ = proj3d.proj_transform(p_x, p_y, p_z, ax.get_proj())
        [str_x, str_y, str_z] = ['{0:.4f}'.format(n) for n in [p_x, p_y, p_z]]
        label = plt.annotate(
            "f(" + str_x + ", " + str_y + ") = " + str_z,
            xy = (x2, y2), xytext = (-20, -20),
            textcoords = 'offset points', ha = 'right', va = 'bottom',
            bbox = dict(boxstyle = 'round,pad=0.5', fc = 'white', alpha = 1.0),
            arrowprops = dict(arrowstyle = '->', connectionstyle = 'arc3,rad=0'))
        g_labels_and_points.append((label, p_x, p_y, p_z))

cell_per_dim = 50
)";
    static string const python_code_footer = R"(
trisurf_plot(g_ax, domain_1, domain_2, object_function, [value_1, value_2, minimum], cell_per_dim)
g_fig.canvas.mpl_connect('motion_notify_event', update_position)

plt.show()
plt.subplots_adjust(left=0.1, right=0.9, top=0.9, bottom=0.1)
)";
    string python_code_main = generate_py_visualization_string(f, var_map, minimum_name);

   Py_Initialize();
   PyRun_SimpleString((python_code_header + "\n" + python_code_main + "\n" + python_code_footer).c_str());
   Py_Exit(0);
}
#else
void visualize_result_via_python(Enode * const, unordered_map<string, Enode *> const &, string const &) {
    cerr << "Sorry. No python was deteced during compilation and visualization is disabled." << endl;
}
#endif
}
