(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ 4968. 390625.) (* skoX (+ (/ (- 1863.) 1220703125.) (* skoX (+ (/ 1863. 15258789062500.) (* skoX (+ (/ (- 39123.) 6103515625000000000.) (* skoX (+ (/ 16767. 76293945312500000000000.) (* skoX (/ (- 16767.) 3814697265625000000000000000.)))))))))))) (/ 6624. 125.))) (and (not (<= skoX 0.)) (or (not (<= (* skoC (/ (- 235.) 42.)) skoS)) (not (<= skoS (* skoC (/ (- 235.) 42.))))))))
(set-info :status unsat)
(check-sat)
