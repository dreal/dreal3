(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= (/ (- 12500.) 3.) skoX) (and (<= (* skoC (/ 3. 13.)) skoS) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))
(set-info :status sat)
(check-sat)
