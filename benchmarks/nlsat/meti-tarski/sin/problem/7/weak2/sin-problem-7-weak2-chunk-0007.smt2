(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoA () Real)
(declare-fun pi () Real)
(assert (and (<= (/ 31415927. 10000000.) pi) (and (not (<= (* pi (/ 1. 2.)) skoA)) (and (not (<= skoX 0.)) (not (<= skoA skoX))))))
(set-info :status sat)
(check-sat)
