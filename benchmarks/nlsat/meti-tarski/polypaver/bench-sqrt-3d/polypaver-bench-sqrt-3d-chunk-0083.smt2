(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= skoX 1.) (and (<= skoY 1.) (and (<= skoZ 1.) (and (not (<= (* skoZ (* skoY (* skoX (/ (- 1.) 2.)))) (/ (- 1.) 4.))) (and (not (<= (* skoZ skoY) 0.)) (and (<= skoZ 2.) (and (<= skoY 2.) (and (<= skoX 2.) (and (<= 1. skoZ) (and (<= 1. skoY) (<= 1. skoX))))))))))))
(set-info :status unsat)
(check-sat)
