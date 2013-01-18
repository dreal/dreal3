(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= skoX (/ 1000. 19.)) (and (not (<= skoX 0.)) (and (<= (* skoC (/ 1770. 689.)) skoS) (and (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (not (<= skoS (* skoC (/ 1770. 689.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))
(set-info :status sat)
(check-sat)
