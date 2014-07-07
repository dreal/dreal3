#include <algorithm>
#include <iostream>
#include "util/infix_iterator.h"
#include "new_realpaver/interval.h"
#include "new_realpaver/unionInterval.h"

using std::copy;
using std::ostream;

namespace realpaver {

void unionInterval::insert(interval const & i) {
    if (i.isEmpty()) { return; }
    if (isEmpty()) { m_list.push_back(i); return; }
    for (list::iterator it = m_list.begin(); it != m_list.end();) {
        //  i:           [       ]
        // it:  [                       ]
        if (it->includes(i)) {
            return;
        }
        //  i:             [            ]
        // it:  [       ]
        if (it->sup < i.inf) {
            it++; continue;
        }
        //  i:  [       ]
        // it:             [            ]
        if (i.sup < it->inf) {
            m_list.insert(it, i);
            return;
        }
        //      i :           [                             ]
        // m_list : [     ]      [  it    ]  [      ]    [     ]  [  ]
        // m_list': [     ]   [    it                       ]
        //                                  [      ]    [     ]  [  ]
        double const new_inf = std::min(i.inf, it->inf);
        double const new_sup = std::max(i.sup, it->sup);
        list::iterator const to_update = it;
        to_update->inf = new_inf;
        to_update->sup = new_sup;
        it++;
        while (it != m_list.end()) {
            //        [     to_update      ]
            //           [ it  ]
            if (it->sup <= new_sup) { it = m_list.erase(it); continue; }
            //        [     to_update      ]
            //                               [ it  ]
            if (new_sup < it->inf) {
                return;
            }
            //        [     to_update      ]
            //                          [ it  ]
            to_update->sup = it->sup;
            m_list.erase(it);
            return;
        }
        return;
    }
    m_list.push_back(i);
}

void unionInterval::insert(unionInterval const & u) {
    // TODO(soonhok): currently, it's O(n^2). Can implmenet O(n) algorithm.
    for (interval const &i : u) { insert(i); }
}

interval unionInterval::hull() const {
    if (m_list.empty()) { return interval::empty; }
    return interval(m_list.front().inf, m_list.back().sup);
}

unionInterval intervalExtendedDiv(interval const & i1, interval const & i2) {
    if (i2.inf < 0.0 && 0.0 < i2.sup) {
        // i2 contains 0
        if (i1.inf > 0.0) {
            // i1 positive
            interval aux1;
            ROUND_UPWARD();
            // [-oo, i1.inf / i2.inf]
            aux1.sup = i1.inf / i2.inf;
            interval aux2;
            ROUND_DOWNWARD();
            // [i1.inf / i2.sup, +oo]
            aux2.inf = i1.inf / i2.sup;
            return unionInterval({aux1, aux2});
        } else if (i1.sup < 0.0) {
            // i1 negative
            interval aux1;
            ROUND_UPWARD();
            // [-oo, i1.sup / i2.sup]
            aux1.sup = i1.sup / i2.sup;
            interval aux2;
            ROUND_DOWNWARD();
            // [i1.sup / i2.inf, +oo]
            aux2.inf = i1.sup / i2.inf;
            return unionInterval({aux1, aux2});
        } else {
            // i1 contains zero
            return unionInterval(interval());
        }
    } else {
        /* standard division */
        return unionInterval(i1 / i2);
    }
}

ostream& operator<<(ostream& out, unionInterval const & u) {
    out << "{";
    copy(u.m_list.begin(), u.m_list.end(), infix_ostream_iterator<interval>(out, ","));
    out << "}";
    return out;
}
}
