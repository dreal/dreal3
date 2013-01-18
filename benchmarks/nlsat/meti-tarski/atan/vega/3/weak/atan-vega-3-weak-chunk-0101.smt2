(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= (* skoX (* skoX (- 1.))) 3.)) (and (not (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (+ (/ (- 3.) 4.) (* skoX (* skoX (+ (/ (- 1.) 4.) (* skoX (- 1.)))))) (* skoY (+ (* skoX (+ (/ 3. 4.) (* skoX (+ (- 3.) (* skoX (/ 1. 4.)))))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
