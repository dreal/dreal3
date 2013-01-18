(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= skoS (* skoC (/ 1770. 689.)))) (not (<= skoX 0.))))
(set-info :status sat)
(check-sat)
