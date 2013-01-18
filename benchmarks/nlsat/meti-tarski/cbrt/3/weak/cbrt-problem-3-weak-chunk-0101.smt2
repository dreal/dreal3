(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoZ (+ (+ (+ 13. (* skoX 10.)) (* skoY 10.)) (* skoZ 10.))) (+ (+ (- 4.) (* skoX (- 5.))) (* skoY (- 5.)))) (and (not (<= skoZ (/ 1. 20.))) (and (not (<= skoY (/ 1. 20.))) (and (not (<= skoX (/ 1. 20.))) (and (not (<= 15. skoZ)) (and (not (<= 15. skoY)) (not (<= 15. skoX)))))))))
(set-info :status unsat)
(check-sat)
