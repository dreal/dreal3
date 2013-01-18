(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= skoY (* skoX 10.)) (and (not (<= (* skoX 10.) skoY)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 2.))) (and (<= (/ 1. 20.) skoX) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
