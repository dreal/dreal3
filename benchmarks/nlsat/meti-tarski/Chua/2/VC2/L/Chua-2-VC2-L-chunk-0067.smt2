(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ 8352. 625.) (* skoX (+ (/ 15138. 390625.) (* skoX (+ (/ 73167. 976562500.) (* skoX (+ (/ 14852901. 156250000000000.) (* skoX (+ (/ 61533447. 781250000000000000.) (* skoX (/ 594823321. 15625000000000000000000.)))))))))))) (- 2304.)) (and (<= skoX 0.) (and (<= skoS (* skoC (/ 76. 15.))) (and (or (not (<= (* skoC (/ 76. 15.)) skoS)) (not (<= skoS (* skoC (/ 76. 15.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))))
(set-info :status unsat)
(check-sat)
