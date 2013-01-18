(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (- 13.) (* skoX (- 10.))) (* skoY (+ (+ (- 36.) (* skoX (- 20.))) (* skoY (- 20.))))) (* skoZ (+ (- 10.) (* skoY (- 20.)))))) (+ (+ 4. (* skoX 5.)) (* skoY (+ (+ 13. (* skoX 10.)) (* skoY 10.)))))) (and (not (<= skoZ (/ 1. 20.))) (and (not (<= skoY (/ 1. 20.))) (and (not (<= skoX (/ 1. 20.))) (and (not (<= 15. skoZ)) (and (not (<= 15. skoY)) (not (<= 15. skoX)))))))))
(set-info :status unsat)
(check-sat)
