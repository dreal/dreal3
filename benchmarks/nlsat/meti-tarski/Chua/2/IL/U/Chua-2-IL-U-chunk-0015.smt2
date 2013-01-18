(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 39888.) 625.) (* skoX (+ (/ 690561. 781250.) (* skoX (+ (/ (- 63761799.) 7812500000.) (* skoX (+ (/ 123634128261. 2500000000000000.) (* skoX (+ (/ (- 4892379075471.) 25000000000000000000.) (* skoX (/ 451729667968489. 1000000000000000000000000.)))))))))))) (- 2304.)) (and (<= skoX 0.) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))
(set-info :status unsat)
(check-sat)
