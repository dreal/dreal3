(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (* skoY (+ (* skoX (/ 1. 2.)) (* skoY (* skoX (/ 1. 2.)))))) (+ (/ (- 1.) 4.) (* skoY (/ (- 1.) 4.))))) (and (or (not (<= skoX 1.)) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))) (or (not (<= skoY 1.)) (not (<= skoZ 1.))))))
(set-info :status sat)
(check-sat)
