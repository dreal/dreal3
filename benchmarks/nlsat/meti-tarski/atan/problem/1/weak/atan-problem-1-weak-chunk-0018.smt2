(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoY (- 3.)) skoZ) (and (<= (* skoY (* skoX (- 8.))) 0.) (and (<= skoZ (* skoY (- 3.))) (and (= (* skoZ skoZ) (+ 75. (* skoX (* skoX 80.)))) (and (= (* skoY skoY) 3.) (and (<= skoX 1.) (and (<= 0. skoZ) (and (<= 0. skoY) (not (<= skoX 0.)))))))))))
(set-info :status unsat)
(check-sat)
