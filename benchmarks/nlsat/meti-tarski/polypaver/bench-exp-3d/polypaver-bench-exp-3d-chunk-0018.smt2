(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (<= (+ (* skoX (- 1.)) (* skoY (- 1.))) skoZ)))
(set-info :status sat)
(check-sat)
