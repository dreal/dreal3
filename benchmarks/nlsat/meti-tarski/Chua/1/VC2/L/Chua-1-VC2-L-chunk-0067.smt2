(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= skoS (* skoC (/ 3. 13.))) (and (not (<= skoX 0.)) (and (<= skoS (* skoC (/ 3. 13.))) (and (or (not (<= (* skoC (/ 3. 13.)) skoS)) (not (<= skoS (* skoC (/ 3. 13.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))
(set-info :status sat)
(check-sat)
