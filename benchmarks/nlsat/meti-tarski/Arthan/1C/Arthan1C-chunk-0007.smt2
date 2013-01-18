(set-logic QF_NRA)

(declare-fun skoCOSS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoS () Real)
(assert (and (not (= (* skoSINS skoSINS) (+ 1. (* skoCOSS (* skoCOSS (- 1.)))))) (<= (/ 217. 100.) skoS)))
(set-info :status sat)
(check-sat)
