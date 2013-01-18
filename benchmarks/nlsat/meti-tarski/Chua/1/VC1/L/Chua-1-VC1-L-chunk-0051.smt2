(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoC (/ 1770. 689.)) skoS) (and (<= (* skoX (+ (/ 55157. 10500.) (* skoX (/ 1002497. 63000000.)))) (/ (- 11108.) 21.)) (and (not (<= skoX 0.)) (and (or (<= skoS (* skoC (/ 1770. 689.))) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))
(set-info :status unsat)
(check-sat)
