(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(assert (and (<= (+ (+ 1. (* skoX (- 1.))) (* skoY (- 1.))) skoZ) (and (<= skoX (/ (- 1.) 2.)) (and (not (<= skoZ 0.)) (and (not (<= skoY 0.)) (not (<= skoX 0.)))))))
(set-info :status unsat)
(check-sat)
