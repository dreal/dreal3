(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (+ (+ (/ 87. 50.) (* skoC (/ 1653. 1250.))) (* skoS (/ (- 261.) 1000.))) (* skoX (+ (+ (/ 841. 500000.) (* skoC (/ (- 15979.) 12500000.))) (* skoS (/ 2523. 10000000.)))))) (+ (+ (- 600.) (* skoC 456.)) (* skoS (- 90.))))) (and (not (<= skoS (* skoC (/ 76. 15.)))) (and (not (<= skoX 0.)) (and (<= skoS (* skoC (/ 76. 15.))) (and (or (not (<= (* skoC (/ 76. 15.)) skoS)) (not (<= skoS (* skoC (/ 76. 15.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
