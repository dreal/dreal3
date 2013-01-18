(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoX (+ (/ (- 4968.) 390625.) (* skoX (+ (/ 1863. 1220703125.) (* skoX (+ (/ (- 1863.) 15258789062500.) (* skoX (+ (/ 39123. 6103515625000000000.) (* skoX (+ (/ (- 16767.) 76293945312500000000000.) (* skoX (/ 16767. 3814697265625000000000000000.)))))))))))) (/ (- 6624.) 125.))) (and (<= skoS (* skoC (/ (- 235.) 42.))) (and (or (not (<= (* skoC (/ (- 235.) 42.)) skoS)) (not (<= skoS (* skoC (/ (- 235.) 42.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))
(set-info :status sat)
(check-sat)
