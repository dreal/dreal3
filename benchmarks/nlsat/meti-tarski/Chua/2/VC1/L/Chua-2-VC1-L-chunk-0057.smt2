(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ (- 87.) 2500.) (* skoX (/ (- 841.) 25000000.)))) 12.)) (or (not (<= (* skoC (/ 400. 441.)) skoS)) (not (<= skoS (* skoC (/ 400. 441.)))))))
(set-info :status unsat)
(check-sat)
