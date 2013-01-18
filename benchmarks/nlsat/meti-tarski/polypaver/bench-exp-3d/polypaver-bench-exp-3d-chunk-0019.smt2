(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* skoX (- 1.)) (* skoY (- 1.))) skoZ)) (and (<= skoZ 1.) (and (<= skoY 1.) (and (<= skoX 1.) (and (<= 0. skoZ) (and (<= 0. skoY) (<= 0. skoX))))))))
(set-info :status unsat)
(check-sat)
