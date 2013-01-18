(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoC (/ (- 235.) 42.)) skoS) (and (not (<= skoS (* skoC (/ (- 235.) 42.)))) (and (<= skoX 289.) (<= 0. skoX)))))
(set-info :status sat)
(check-sat)
