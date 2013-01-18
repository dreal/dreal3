(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (+ 1. (* skoX (- 1.))) (* skoY (- 1.))) skoZ) (and (<= skoZ (+ (+ (/ (- 32.) 5.) (* skoX (- 1.))) (* skoY (- 1.)))) (and (not (<= skoZ (/ 1. 20.))) (and (not (<= skoY (/ 1. 20.))) (and (not (<= skoX (/ 1. 20.))) (and (not (<= 15. skoZ)) (and (not (<= 15. skoY)) (not (<= 15. skoX))))))))))
(set-info :status unsat)
(check-sat)
