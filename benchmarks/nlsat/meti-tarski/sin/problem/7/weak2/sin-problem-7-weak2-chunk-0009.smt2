(set-logic QF_NRA)

(declare-fun pi () Real)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(assert (and (<= pi (/ 15707963. 5000000.)) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= (* pi (/ 1. 2.)) skoA)) (and (not (<= skoX 0.)) (not (<= skoA skoX)))))))
(set-info :status sat)
(check-sat)
