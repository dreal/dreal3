(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (- 6000.) (* skoX (- 1000000.)))) 12.) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX (/ 4. 5.)) (<= (/ 1. 500.) skoX)))))
(set-info :status sat)
(check-sat)
