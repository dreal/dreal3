(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (* skoY (- 1.))) 0.)) (not (<= (* skoZ (* skoY (* skoX (/ 1. 2.)))) (/ 1. 4.)))))
(set-info :status sat)
(check-sat)
