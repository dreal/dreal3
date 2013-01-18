(set-logic QF_NRA)

(declare-fun skoCOSS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoM () Real)
(declare-fun skoS () Real)
(assert (and (not (= (* skoSINS skoSINS) (+ 1. (* skoCOSS (* skoCOSS (- 1.)))))) (and (<= 2. skoS) (<= 2. skoM))))
(set-info :status sat)
(check-sat)
