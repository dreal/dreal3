(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (<= skoZ 1.) (and (not (<= (* skoZ (* skoY (- 1.))) 0.)) (and (not (<= skoY 1.)) (and (<= skoZ 2.) (and (<= skoY 2.) (and (<= skoX 2.) (and (<= 1. skoZ) (and (<= 1. skoY) (<= 1. skoX))))))))))
(set-info :status unsat)
(check-sat)
