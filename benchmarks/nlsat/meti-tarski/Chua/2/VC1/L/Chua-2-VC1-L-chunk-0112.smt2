(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ (- 8352.) 625.) (* skoX (+ (/ (- 15138.) 390625.) (* skoX (+ (/ (- 73167.) 976562500.) (* skoX (+ (/ (- 14852901.) 156250000000000.) (* skoX (+ (/ (- 61533447.) 781250000000000000.) (* skoX (/ (- 594823321.) 15625000000000000000000.)))))))))))) 2304.)) (or (not (<= (* skoC (/ 400. 441.)) skoS)) (not (<= skoS (* skoC (/ 400. 441.)))))))
(set-info :status unsat)
(check-sat)
