(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoC (/ 3. 13.)) skoS)) (and (not (<= skoX 0.)) (not (<= skoS (* skoC (/ 3. 13.)))))))
(set-info :status unsat)
(check-sat)
