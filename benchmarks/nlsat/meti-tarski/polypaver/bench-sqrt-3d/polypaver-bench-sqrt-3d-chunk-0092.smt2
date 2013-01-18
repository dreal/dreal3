(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoZ (* skoY (- 1.))) 0.) (and (or (not (<= skoX 1.)) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))) (and (<= skoZ 2.) (and (<= skoY 2.) (and (<= skoX 2.) (and (<= 1. skoZ) (and (<= 1. skoY) (<= 1. skoX)))))))))
(set-info :status sat)
(check-sat)
