(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (/ (- 3000.) 19.) skoX)) (and (not (<= skoX 0.)) (not (<= (* skoC (/ 1770. 689.)) skoS)))))
(set-info :status unsat)
(check-sat)
