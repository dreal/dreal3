(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= 0. skoY) (and (<= (* skoX 2000.) skoY) (and (<= skoY 0.) (and (or (not (<= (* skoX 2000.) skoY)) (not (<= skoY (* skoX 2000.)))) (and (not (<= skoY skoX)) (and (not (<= skoX 0.)) (and (not (<= (* pi (/ 1. 2.)) skoY)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))))))))
(set-info :status unsat)
(check-sat)
