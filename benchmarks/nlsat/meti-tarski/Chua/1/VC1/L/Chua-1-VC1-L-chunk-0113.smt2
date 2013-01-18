(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoS (* skoC (/ 1770. 689.)))) (and (not (<= skoX 0.)) (not (<= (* skoC (/ 1770. 689.)) skoS)))))
(set-info :status unsat)
(check-sat)
