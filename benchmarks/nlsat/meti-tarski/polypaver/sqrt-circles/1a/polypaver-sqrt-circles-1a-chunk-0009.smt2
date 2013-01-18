(set-logic QF_NRA)

(declare-fun skoS1 () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoS2 () Real)
(assert (and (= (* skoY (+ 2. (* skoY (- 1.)))) (+ (+ 1. (* skoS1 (* skoS1 (- 1.)))) (* skoX skoX))) (and (<= skoS1 1.) (and (<= 0. skoS1) (not (<= skoS2 2.))))))
(set-info :status sat)
(check-sat)
