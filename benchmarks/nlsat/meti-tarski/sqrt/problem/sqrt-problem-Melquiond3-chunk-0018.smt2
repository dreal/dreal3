(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY)))
(set-info :status sat)
(check-sat)
