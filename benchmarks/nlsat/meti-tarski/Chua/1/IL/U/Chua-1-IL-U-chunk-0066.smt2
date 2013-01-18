(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ 1728. 3125.) (* skoX (+ (/ (- 648.) 9765625.) (* skoX (+ (/ 162. 30517578125.) (* skoX (+ (/ (- 1701.) 6103515625000000.) (* skoX (+ (/ 729. 76293945312500000000.) (* skoX (/ (- 729.) 3814697265625000000000000.)))))))))))) 2304.)) (and (not (<= skoX 0.)) (or (not (<= (* skoC (/ (- 235.) 42.)) skoS)) (not (<= skoS (* skoC (/ (- 235.) 42.))))))))
(set-info :status unsat)
(check-sat)
