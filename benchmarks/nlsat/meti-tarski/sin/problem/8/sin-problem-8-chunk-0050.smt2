(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= 0. skoY) (and (not (= skoY 0.)) (and (not (<= (* skoY (+ (+ 1. (* pi (/ (- 1.) 2.))) (* skoY (* skoY (* pi (/ 1. 12.)))))) 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= (* pi (/ 1. 2.)) skoY)) (and (not (<= skoX 0.)) (not (<= skoY skoX))))))))))
(set-info :status sat)
(check-sat)
