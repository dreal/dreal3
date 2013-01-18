(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoX (/ 1000. 19.))) (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (not (<= skoS (* skoC (/ 1770. 689.)))))))
(set-info :status sat)
(check-sat)
