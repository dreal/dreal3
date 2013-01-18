(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoY (- 3.)) skoZ)) (and (= (* skoZ skoZ) (+ 75. (* skoX (* skoX 80.)))) (and (= (* skoY skoY) 3.) (and (<= skoX 1.) (and (<= 0. skoZ) (and (<= 0. skoY) (not (<= skoX 0.)))))))))
(set-info :status unsat)
(check-sat)
