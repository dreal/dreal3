(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ 57. 500.) (* skoX (/ 361. 1000000.)))) (- 12.)) (and (<= skoS (* skoC (/ 3. 13.))) (and (not (<= (* skoX (+ (/ 25764. 875.) (* skoX (/ 323817. 3500000.)))) (/ (- 21528.) 7.))) (and (not (<= skoX 0.)) (and (or (<= (* skoC (/ 3. 13.)) skoS) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
