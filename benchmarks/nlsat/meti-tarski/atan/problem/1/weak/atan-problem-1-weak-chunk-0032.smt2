(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (* skoX 3.)) (* skoY (* skoX (+ 15. (* skoX (* skoX 8.))))))) (not (<= skoX 0.))))
(set-info :status sat)
(check-sat)
