(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (/ 760000. 7383.) (* skoC (/ (- 3400.) 7383.))) skoS)) (not (<= skoX (/ 177. 366500000.)))))
(set-info :status sat)
(check-sat)
