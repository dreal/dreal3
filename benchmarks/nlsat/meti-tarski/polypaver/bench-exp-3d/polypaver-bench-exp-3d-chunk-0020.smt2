(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (not (<= skoZ (+ (* skoX (- 1.)) (* skoY (- 1.))))))
(set-info :status sat)
(check-sat)
