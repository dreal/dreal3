(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ (- 1728.) 3125.) (* skoX (+ (/ 648. 9765625.) (* skoX (+ (/ (- 162.) 30517578125.) (* skoX (+ (/ 1701. 6103515625000000.) (* skoX (+ (/ (- 729.) 76293945312500000000.) (* skoX (/ 729. 3814697265625000000000000.)))))))))))) (- 2304.)) (and (<= skoX 0.) (and (not (<= (* skoC (/ 1770. 689.)) skoS)) (and (not (<= (* skoC (/ 1770. 689.)) skoS)) (and (<= skoS (* skoC (/ 1770. 689.))) (and (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (<= skoX 0.)) (and (or (<= skoS (* skoC (/ 1770. 689.))) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))))
(set-info :status unsat)
(check-sat)
