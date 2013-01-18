(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= skoZ (* skoY (- 3.)))) (not (<= skoX 0.))))
(set-info :status sat)
(check-sat)
