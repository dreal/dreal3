(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 8316.) 1953125.) (* skoX (+ (/ 6237. 12207031250.) (* skoX (+ (/ (- 6237.) 152587890625000.) (* skoX (+ (/ 130977. 61035156250000000000.) (* skoX (+ (/ (- 56133.) 762939453125000000000000.) (* skoX (/ 56133. 38146972656250000000000000000.)))))))))))) (/ (- 11088.) 625.)) (and (<= skoX 0.) (and (<= skoS (* skoC (/ 3. 13.))) (and (or (not (<= (* skoC (/ 3. 13.)) skoS)) (not (<= skoS (* skoC (/ 3. 13.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))
(set-info :status unsat)
(check-sat)
