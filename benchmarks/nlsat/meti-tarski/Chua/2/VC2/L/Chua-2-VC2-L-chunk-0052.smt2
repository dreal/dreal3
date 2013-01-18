(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (+ (* skoC (/ (- 798.) 125.)) (* skoS (/ 63. 50.))) (* skoX (+ (* skoC (/ 931. 31250.)) (* skoS (/ (- 147.) 25000.)))))) (+ (* skoC (- 456.)) (* skoS 90.))) (and (<= skoX 0.) (and (<= skoS (* skoC (/ 76. 15.))) (and (or (not (<= (* skoC (/ 76. 15.)) skoS)) (not (<= skoS (* skoC (/ 76. 15.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))))
(set-info :status unsat)
(check-sat)
