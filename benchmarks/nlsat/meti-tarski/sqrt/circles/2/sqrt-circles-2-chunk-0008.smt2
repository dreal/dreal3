(set-logic QF_NRA)

(declare-fun skoD () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (<= (* skoY (+ (+ 2. (* skoD 2.)) (* skoY (- 1.)))) (+ (+ 1. (* skoD (+ 2. skoD))) (* skoX skoX)))))
(set-info :status unsat)
(check-sat)
