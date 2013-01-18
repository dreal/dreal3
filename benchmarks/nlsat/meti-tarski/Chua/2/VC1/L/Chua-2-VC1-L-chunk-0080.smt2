(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoS (* skoC (/ 400. 441.)))) (and (not (<= skoX 0.)) (or (not (<= (* skoC (/ 400. 441.)) skoS)) (not (<= skoS (* skoC (/ 400. 441.))))))))
(set-info :status sat)
(check-sat)
