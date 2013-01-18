(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(assert (not (<= (* skoY (+ (* skoA (- 2.)) skoY)) (* skoX (* skoX (- 1.))))))
(set-info :status sat)
(check-sat)
