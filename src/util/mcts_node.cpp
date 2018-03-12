/*********************************************************************
Author: Daniel Bryce <dbryce@sift.net>

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

#include <assert.h>
#include <math.h>
#include <limits>

#include "util/logging.h"
#include "util/mcts_expander.h"
#include "util/mcts_node.h"

using dreal::mcts_node;
using dreal::icp_mcts_node;
using std::numeric_limits;
using std::shared_ptr;

mcts_node::~mcts_node() {
    // DREAL_LOG_INFO << "mcts_node::delete()";
    DREAL_LOG_INFO << "mcts_node::delete(" << m_id << ")";

    auto parent_p = m_parent.lock();
    if (parent_p) DREAL_LOG_DEBUG << "Parent is: " << parent_p->id();

    // remove parent w/o any children
    if (auto par = m_parent.lock()) {
        DREAL_LOG_INFO << "mcts_node::delete(" << m_id << ") parent " << par->id();
        m_parent.reset();
        vector<shared_ptr<mcts_node>> * parent_children = par->children();
        // auto it = std::find(parent_children->begin(), parent_children->end(),
        // shared_ptr<mcts_node>(this));
        //   if (it != parent_children->end()) {
        //        DREAL_LOG_INFO << "deleting " << m_parent->id() << " pointer to " << m_id;
        //        parent_children->erase(it);
        //   }
        //      DREAL_LOG_INFO << m_parent->id() << " has " << parent_children->size() << "
        // children";
        if (parent_children->empty()) {
            //    shared_ptr<mcts_node> parent (m_parent);
            // m_parent.reset();
            // delete m_parent;

            if (auto gpar = par->parent().lock()) {
                vector<shared_ptr<mcts_node>> * grandparent_children = gpar->children();
                auto it =
                    std::find(grandparent_children->begin(), grandparent_children->end(), par);
                grandparent_children->erase(it);
            }
        }
    }

    // // remove children
    // if (!m_children_list.empty()) {
    //    DREAL_LOG_INFO << "mcts_node::delete(" << m_id << ") children";
    //     // for (auto child : m_children_list) {
    //  //      if(child){
    //  //    DREAL_LOG_INFO << "deleting " << child->id() << " pointer to " << m_id;
    //  //    // child->set_parent(nullptr);
    //  //    //DREAL_LOG_INFO << "child parent " << child->parent();
    //  // //     //m_size -= child->size()+1;
    //  // //   child.reset();
    //  // //     //child = NULL;
    //     // //     //delete child;
    //  //    child = nullptr;
    //     //  }
    //  //  }
    //    m_children_list.clear();

    // }
    //   DREAL_LOG_INFO << "mcts_node::delete(" << m_id << ") exit";
}

shared_ptr<mcts_node> mcts_node::select() {
    shared_ptr<mcts_node> selected;
    double max_score = numeric_limits<double>::lowest();

    // UCT score
    for (auto child : m_children_list) {
        // DREAL_LOG_INFO << m_value << " " << m_visits << " " << child->value() << " "
        //                      << child->visits() << " " << max_score;
        double score = (child->value() / child->visits()) +
                       UCT_COEFFICIENT * sqrt(log(m_visits) / child->visits());
        child->set_score(score);
        DREAL_LOG_INFO << "mcts_node::select(" << m_id << ") set score(" << child->id()
                       << ") = " << score << " " << (child->value() / child->visits()) << " "
                       << (sqrt(log(m_visits) / child->visits()));

        if (score > max_score) {
            selected = child;
            max_score = score;
        }
    }

    DREAL_LOG_INFO << "mcts_node::select(" << m_id << ") = " << selected->id()
                   << ", score = " << max_score;
    return selected;
}

shared_ptr<mcts_node> icp_mcts_node::expand() {
    DREAL_LOG_INFO << "mcts_node::expand(" << m_id << ") ";

    if (!m_children_list.empty()) {
        // then have an unexplored child that was already generated
        for (auto child : m_children_list) {
            if (child->visits() == 0) return child;
        }
    }

    shared_ptr<mcts_node> max_child;
    //    double max_score = 0.0;
    if (!m_terminal) {
        m_expander->expand(m_this);
        m_size = m_children_list.size();

        DREAL_LOG_INFO << "mcts_node::expand(" << m_id << ")"
                       << " Got num children: " << m_children_list.size();

        if (m_children_list.empty()) {
            m_terminal = true;
        }
        // else {
        //       for (shared_ptr<mcts_node> child : m_children_list) {
        //         DREAL_LOG_INFO << "child: " << child->id() << " count = " << child.use_count();
        //         child->inc_visits();
        //         double score = child->simulate();
        //         DREAL_LOG_INFO << "child: " << child->id() << " count = " << child.use_count();
        //         if(!max_child || score > max_score){
        //           max_child = child;
        //           max_score = score;
        //         }
        //       }
        // }
    }
    if (  //! max_child &&
        !m_terminal) {
        max_child = m_children_list[0];
    }

    DREAL_LOG_INFO << "mcts_node::expand(" << m_id << ") exit";

    return (m_terminal ? nullptr  // (m_is_solution ? this : NULL)
                       : max_child);
}

double mcts_node::simulate() {
    DREAL_LOG_INFO << "mcts_node::simulate(" << m_id << ")";
    if (m_terminal && !m_is_solution) {
        m_value = numeric_limits<double>::lowest();
    } else {
        m_value = ((m_value * m_visits) + m_expander->simulate(m_this)) / (m_visits + 1);
        // m_value = (m_value+ m_expander->simulate(this))/2;
    }
    DREAL_LOG_INFO << "mcts_node::simulate(" << m_id << ") exit";
    return m_value;
}

void mcts_node::backpropagate() {
    // DREAL_LOG_INFO << "mcts_node::backpropagate(" << m_id << ") size = " << m_size;
    m_visits++;
    if (!m_children_list.empty()) {
        m_visits++;
        m_size = 0;
        m_value = 0;
        for (auto child : m_children_list) {
            m_size += child->size() + 1;
            m_value += child->value();
        }
        m_value /= m_children_list.size();  // average value backprop
    } else {
        // m_visits = 1;
        //   m_size = 0;
        //   m_value = numeric_limits<double>::lowest();
    }
    DREAL_LOG_INFO << "mcts_node::backpropagate(" << m_id << ") size = " << m_size
                   << " value = " << m_value;
}

void icp_mcts_node::draw_dot(ostream & out) {
    auto parent_p = m_parent.lock();
    bool is_root = (!parent_p);
    out.precision(2);
    if (is_root) {
        out << "digraph icp_mcts_graph {\n";
    }

    for (auto child : m_children_list) {
        out << "\"" << this->id() << " : " << this->visits() << " : " << this->value() << "\" -> \""
            << child->id() << " : " << child->visits() << " : " << child->value() << "\" [label=\""
            << child->score() << "\"];\n";
        child->draw_dot(out);
    }

    if (is_root) {
        out << "}";
    }
}
