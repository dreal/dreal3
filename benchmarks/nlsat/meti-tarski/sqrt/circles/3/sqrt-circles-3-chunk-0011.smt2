(set-logic QF_NRA)

(declare-fun skoD () Real)
(declare-fun skoA () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (<= (* skoY (+ (+ (* skoA 2.) (* skoD 2.)) (* skoY (- 1.)))) (+ (+ (* skoA skoA) (* skoD (+ (* skoA 2.) skoD))) (* skoX skoX)))))
(set-info :status unsat)
(check-sat)
