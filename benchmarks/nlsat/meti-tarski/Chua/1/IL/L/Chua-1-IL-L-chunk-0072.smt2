(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoC (/ (- 235.) 42.)) skoS)) (not (<= (* skoX (+ (/ 207. 6250000.) (* skoX (/ (- 207.) 156250000000.)))) (/ 69. 250.)))))
(set-info :status unsat)
(check-sat)
