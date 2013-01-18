(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= skoS (+ (/ 760000. 7383.) (* skoC (/ (- 3400.) 7383.))))) (not (<= skoX (/ 177. 366500000.)))))
(set-info :status sat)
(check-sat)
