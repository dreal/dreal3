(set-logic QF_NRA)

(declare-fun skoD () Real)
(declare-fun skoY () Real)
(declare-fun skoS1 () Real)
(declare-fun skoS2 () Real)
(declare-fun skoX () Real)
(assert (and (= (* skoY (+ (+ 2. (* skoD 2.)) (* skoY (- 1.)))) (+ (+ (+ 1. (* skoD (+ 2. skoD))) (* skoS2 (* skoS2 (- 1.)))) (* skoX skoX))) (and (= (* skoY (+ 2. (* skoY (- 1.)))) (+ (+ 1. (* skoS1 (* skoS1 (- 1.)))) (* skoX skoX))) (and (not (<= skoS2 (+ 1. skoD))) (and (<= skoS1 1.) (and (<= 0. skoS2) (and (<= 0. skoS1) (<= 0. skoD))))))))
(set-info :status unsat)
(check-sat)

