(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (- 1.) skoX) (and (= (* skoY skoY) 3.) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= 0. skoY) (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
