(set-logic QF_NRA)

(declare-fun pi () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= skoY skoX)) (and (not (<= skoX 0.)) (and (not (<= (* pi (/ 1. 2.)) skoY)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))))
(set-info :status unsat)
(check-sat)
