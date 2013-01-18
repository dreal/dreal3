(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (<= (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.))) skoZ)))
(set-info :status sat)
(check-sat)
