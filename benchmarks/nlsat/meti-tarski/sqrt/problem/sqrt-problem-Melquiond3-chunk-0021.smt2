(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(assert (not (= (+ (* skoSXY (- 1.)) (* skoT (* skoT skoSXY))) skoX)))
(set-info :status sat)
(check-sat)
