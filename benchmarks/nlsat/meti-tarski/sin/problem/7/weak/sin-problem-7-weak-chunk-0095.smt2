(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= 0. skoX)) (and (not (= skoY 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= (* pi (/ 1. 2.)) skoY)) (and (not (<= skoX 0.)) (and (not (<= skoY skoX)) (or (not (<= (* skoX 2000.) skoY)) (not (<= skoY (* skoX 2000.))))))))))))
(set-info :status unsat)
(check-sat)
