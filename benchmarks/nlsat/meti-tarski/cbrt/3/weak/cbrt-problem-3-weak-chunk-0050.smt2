(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= skoZ (+ (+ (/ (- 32.) 5.) (* skoX (- 1.))) (* skoY (- 1.)))) (and (not (<= (+ (+ 1. (* skoX (- 1.))) (* skoY (- 1.))) skoZ)) (and (not (<= skoZ (/ 1. 20.))) (and (not (<= skoY (/ 1. 20.))) (and (not (<= skoX (/ 1. 20.))) (and (not (<= 15. skoZ)) (and (not (<= 15. skoY)) (not (<= 15. skoX))))))))))
(set-info :status unsat)
(check-sat)
