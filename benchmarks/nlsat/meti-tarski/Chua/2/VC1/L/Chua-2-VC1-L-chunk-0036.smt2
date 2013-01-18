(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoC (/ 400. 441.)) skoS)) (and (or (not (<= (* skoC (/ 400. 441.)) skoS)) (not (<= skoS (* skoC (/ 400. 441.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (or (not (<= 0. skoX)) (or (not (<= skoX (/ 1570. 21.))) (<= 0. skoS))) (and (or (not (<= 0. skoX)) (or (not (<= skoX (/ 1570. 21.))) (<= 0. skoC))) (and (<= skoX 75.) (<= 0. skoX))))))))
(set-info :status sat)
(check-sat)
