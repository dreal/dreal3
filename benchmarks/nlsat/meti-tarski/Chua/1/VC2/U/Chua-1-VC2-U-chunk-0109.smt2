(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoX 0.)) (and (not (<= skoS (* skoC (/ 3. 13.)))) (and (<= (* skoC (/ 3. 13.)) skoS) (and (or (not (<= skoS (* skoC (/ 3. 13.)))) (<= skoX 0.)) (and (or (<= (* skoC (/ 3. 13.)) skoS) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status sat)
(check-sat)
