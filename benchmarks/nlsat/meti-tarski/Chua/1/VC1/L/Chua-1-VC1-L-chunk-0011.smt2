(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoC (/ 1770. 689.)) skoS) (and (<= skoS (* skoC (/ 1770. 689.))) (and (<= skoX 289.) (<= 0. skoX)))))
(set-info :status sat)
(check-sat)
