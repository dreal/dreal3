(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoY (+ (* skoX 231.) (* skoY (+ (- 315.) (* skoY (+ (* skoX 315.) (* skoY (+ (- 105.) (* skoY (+ (* skoX 105.) (* skoY (+ (- 5.) (* skoY (* skoX 5.)))))))))))))) 231.)) (and (not (<= 0. skoY)) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
