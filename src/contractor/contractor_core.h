/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, the dReal Team

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
#include <algorithm>
#include <unordered_map>
#include <vector>
#include <cassert>
#include <initializer_list>
#include <stdexcept>
#include <string>
#include <memory>
#include <utility>
#include "./config.h"
#include "constraint/constraint.h"
#include "contractor/contractor_cell.h"
#include "contractor/contractor_status.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"

namespace dreal {
// Wrapper on contractor_cell and its derived classes
class contractor {
private:
    std::shared_ptr<contractor_cell> m_ptr;

public:
    contractor() : m_ptr(nullptr) { }
    explicit contractor(std::shared_ptr<contractor_cell> const c) : m_ptr(c) {
        assert(m_ptr != nullptr);
    }
    contractor(contractor const & c) : m_ptr(c.m_ptr) {
        assert(m_ptr);
    }
    contractor(contractor && c) noexcept : m_ptr(std::move(c.m_ptr)) {}
    ~contractor() noexcept { }

    friend void swap(contractor & c1, contractor & c2) {
        using std::swap;
        swap(c1.m_ptr, c2.m_ptr);
    }

    contractor& operator=(contractor c) {
        swap(*this, c);
        return *this;
    }

    ibex::BitSet get_input() const { return m_ptr->get_input(); }

    void prune(contractor_status & cs) {
        if (m_ptr) {
            // by default, clear output vector and used constraints.
            m_ptr->prune(cs);
            if (cs.m_config.nra_use_stat) {
                cs.m_config.nra_stat.increase_prune();
                if (!cs.m_output.empty()) {
                    cs.m_config.nra_stat.increase_non_trivial_prune();
                }
            }
        }
    }
    void prune_with_assert(contractor_status & cs);
    bool operator==(contractor const & c) const { return m_ptr == c.m_ptr; }
    bool operator<(contractor const & c) const { return m_ptr < c.m_ptr; }
    std::size_t hash() const { return (std::size_t) m_ptr.get(); }
    friend std::ostream & operator<<(std::ostream & out, contractor const & c);
};

}  // namespace dreal

namespace std {
template <>
struct hash<dreal::contractor> {
    std::size_t operator()(dreal::contractor const & c) const { return c.hash(); }
};
}  // namespace std
