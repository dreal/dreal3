(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* pi (/ 1. 4.)) skoY)) (and (<= skoX 120.) (<= 100. skoX))))
(set-info :status sat)
(check-sat)
