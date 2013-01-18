(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* pi (/ 1. 2.)) skoY)) (and (not (<= skoX 0.)) (not (<= skoY skoX)))))
(set-info :status sat)
(check-sat)
