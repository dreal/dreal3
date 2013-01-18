(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoZ (+ (+ (+ 69. (* skoX 10.)) (* skoY 10.)) (* skoZ 10.))) (+ (+ (- 32.) (* skoX (- 5.))) (* skoY (- 5.)))) (and (not (<= skoZ 0.)) (and (not (<= skoY 0.)) (not (<= skoX 0.))))))
(set-info :status unsat)
(check-sat)
