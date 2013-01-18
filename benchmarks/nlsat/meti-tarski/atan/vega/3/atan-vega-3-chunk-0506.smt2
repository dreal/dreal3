(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoY)) (and (not (<= (* skoY (+ (* skoX 63.) (* skoY (+ (- 70.) (* skoY (+ (* skoX 70.) (* skoY (+ (- 15.) (* skoY (* skoX 15.)))))))))) 63.)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)
