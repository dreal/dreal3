(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 207.) 6250000.) (* skoX (/ 207. 156250000000.)))) (/ (- 69.) 250.)) (and (or (not (<= skoS (* skoC (/ (- 235.) 42.)))) (<= skoX 0.)) (and (or (<= (* skoC (/ (- 235.) 42.)) skoS) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))
(set-info :status unsat)
(check-sat)
