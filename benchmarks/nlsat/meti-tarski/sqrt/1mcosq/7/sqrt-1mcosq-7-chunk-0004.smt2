(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= skoY (* pi (/ 1. 2.))) (and (<= (/ 1. 20.) skoX) (not (<= skoY skoX)))))
(set-info :status sat)
(check-sat)
