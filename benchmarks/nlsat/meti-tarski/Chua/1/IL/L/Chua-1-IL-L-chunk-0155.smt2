(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (/ (- 3000.) 19.) skoX)) (and (not (<= skoX 0.)) (not (<= skoS (* skoC (/ (- 235.) 42.)))))))
(set-info :status unsat)
(check-sat)
