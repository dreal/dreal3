(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ (- 13608.) 390625.) (* skoX (+ (/ 5103. 1220703125.) (* skoX (+ (/ (- 5103.) 15258789062500.) (* skoX (+ (/ 107163. 6103515625000000000.) (* skoX (+ (/ (- 45927.) 76293945312500000000000.) (* skoX (/ 45927. 3814697265625000000000000000.)))))))))))) (/ (- 18144.) 125.))) (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (not (<= skoS (* skoC (/ 1770. 689.)))))))
(set-info :status sat)
(check-sat)
