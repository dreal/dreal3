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

#pragma once

#include <stddef.h>
#include <queue>
#include <vector>
#include <iostream>
#include <memory>
#include "util/box.h"
#include "util/logging.h"
#include "util/mcts_expander.h"

using std::vector;
using std::ostream;
using std::shared_ptr;
using std::weak_ptr;
using std::make_shared;

namespace dreal {
class mcts_expander;
class mcts_node;

struct mcts_node_compare {
    bool operator()(const mcts_node * a, const mcts_node * b) { return &a < &b; }
};

static const double UCT_COEFFICIENT = 5.0;
static int id_counter = 0;

class mcts_node {
protected:
    double m_value;   // aggregated value of end games
    double m_score;   // selection ranking value
    int m_size;       // subtree size
    bool m_expanded;  // has it been expanded
    mcts_expander * m_expander;
    bool m_is_solution;
    weak_ptr<mcts_node> m_parent;
    int m_visits;
    bool m_terminal;
    weak_ptr<mcts_node> m_this;
    int m_id;
    vector<shared_ptr<mcts_node>> m_children_list;

public:
    mcts_node(shared_ptr<mcts_node> parent, mcts_expander * expander)
        : m_value(0.0),
          m_score(0.0),
          m_size(0),
          m_expanded(false),
          m_expander(expander),
          m_is_solution(false),
          m_parent(parent),
          m_visits(0),
          m_terminal(false) {
      m_children_list.clear();
        if (auto sp = m_parent.lock()) {
            m_id = id_counter++;
        } else {  // root node
            m_id = -1;
            id_counter = 0;
        }
    }
    explicit mcts_node(mcts_expander * expander) : mcts_node(NULL, expander) {}
    virtual ~mcts_node();

    shared_ptr<mcts_node> select();              // Select a child node
    virtual shared_ptr<mcts_node> expand() = 0;  // Expand a leaf node
    double simulate();                           // Simulate to end of game
    void backpropagate();                        // Backpropagate end game value

    void set_sp(shared_ptr<mcts_node> sp) { m_this = sp; }
    weak_ptr<mcts_node> get_sp() { return m_this; }
    int size() const { return m_size; }
    weak_ptr<mcts_node> parent() const { return m_parent; }
    void set_parent(weak_ptr<mcts_node> parent) { m_parent = parent; }
    double value() const { return m_value; }
    void set_value(double value) { m_value = value; }
    double score() const { return m_score; }
    void set_score(double score) { m_score = score; }
    vector<shared_ptr<mcts_node>> * children() { return &m_children_list; }
    void set_solution(bool sol) { m_is_solution = sol; }
    bool is_solution() const { return m_is_solution; }
    int id() const { return m_id; }
    int visits() const { return m_visits; }
    void inc_visits() { m_visits++; }
    bool terminal() const { return m_terminal; }
    bool has_unexplored_children() const {
        if (m_terminal)
            return false;
        else if (m_children_list.empty())
            return true;

        for (auto child : m_children_list) {
            if (child->visits() == 0) return true;
        }
        return false;
    }
    virtual void draw_dot(ostream & out) = 0;  // create dot file
};

class icp_mcts_node : public mcts_node {
private:
    box m_box;
    vector<box> sat_simulation_boxes;

public:
    icp_mcts_node(box b, mcts_expander * expander) : mcts_node(expander), m_box(b) {}
    icp_mcts_node(box b, shared_ptr<mcts_node> parent, mcts_expander * expander)
        : mcts_node(parent, expander), m_box(b) {}
    ~icp_mcts_node() {}
    virtual shared_ptr<mcts_node> expand();  // Expand a leaf node

    box get_box() const { return m_box; }
    vector<box> get_sat_simulation_boxes() const { return sat_simulation_boxes; }
    void add_sat_simulation_box(box b) { sat_simulation_boxes.push_back(b); }

    virtual void draw_dot(ostream & out);  // create dot file
};

bool operator==(icp_mcts_node const & n1, icp_mcts_node const & n2);
inline bool operator<(mcts_node const & a, mcts_node const & b) { return a.score() < b.score(); }
inline bool operator>(mcts_node const & a, mcts_node const & b) { return a.score() > b.score(); }
}  // namespace dreal
