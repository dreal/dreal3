(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoY (- 3.)) skoZ)) (not (<= skoX 0.))))
(set-info :status sat)
(check-sat)
