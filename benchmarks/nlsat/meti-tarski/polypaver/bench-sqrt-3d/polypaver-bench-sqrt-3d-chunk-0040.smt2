(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= skoZ 1.) (and (not (<= (* skoZ (* skoY (* skoX (/ 1. 2.)))) (/ (- 1.) 4.))) (and (<= skoZ 2.) (and (<= skoY 2.) (and (<= skoX 2.) (and (<= 1. skoZ) (and (<= 1. skoY) (<= 1. skoX)))))))))
(set-info :status sat)
(check-sat)
