(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ 87. 2500.) (* skoX (/ 841. 25000000.)))) (- 12.)) (and (not (<= skoX 0.)) (and (<= skoS (* skoC (/ 76. 15.))) (and (or (not (<= (* skoC (/ 76. 15.)) skoS)) (not (<= skoS (* skoC (/ 76. 15.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))))
(set-info :status unsat)
(check-sat)
