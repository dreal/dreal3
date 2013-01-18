(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (* skoZ (* skoY skoY))) 0.)) (and (not (<= (* skoZ (+ (* skoY (* skoX (/ 1. 4.))) (* skoZ (* skoY (* skoY (* skoX (+ (- 1.) (* skoX (/ 1. 4.))))))))) (/ (- 1.) 16.))) (or (not (<= skoX 1.)) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))))))
(set-info :status sat)
(check-sat)
