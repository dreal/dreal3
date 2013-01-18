(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (or (not (<= 0. skoY)) (or (not (<= (* skoX 10.) skoY)) (or (not (<= skoY 0.)) (not (<= skoY (* skoX 10.)))))) (and (not (<= skoY skoX)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))
(set-info :status sat)
(check-sat)
