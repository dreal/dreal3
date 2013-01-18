(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (not (<= (* skoZ (* skoY (* skoX (/ 1. 2.)))) (/ (- 1.) 4.))))
(set-info :status sat)
(check-sat)
