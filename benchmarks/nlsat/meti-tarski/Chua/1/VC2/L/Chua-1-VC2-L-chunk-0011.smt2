(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoC (/ 3. 13.)) skoS) (and (<= skoS (* skoC (/ 3. 13.))) (and (<= skoX 289.) (<= 0. skoX)))))
(set-info :status sat)
(check-sat)
