(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= skoY (* pi (/ 1. 2.)))) (not (<= skoY skoX))))
(set-info :status sat)
(check-sat)
