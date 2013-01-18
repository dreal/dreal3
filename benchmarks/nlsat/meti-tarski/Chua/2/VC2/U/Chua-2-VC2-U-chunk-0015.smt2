(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 8064.) 125.) (* skoX (+ (/ 14112. 15625.) (* skoX (+ (/ (- 16464.) 1953125.) (* skoX (+ (/ 50421. 976562500.) (* skoX (+ (/ (- 50421.) 244140625000.) (* skoX (/ 117649. 244140625000000.)))))))))))) (- 2304.)) (and (<= skoX 0.) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))
(set-info :status unsat)
(check-sat)
