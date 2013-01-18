(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (+ (* skoX (/ (- 1.) 6.)) (* skoY (* skoY (* skoX (/ 1. 120.))))))) (* skoX (* skoX (* skoX (/ (- 1.) 6.)))))) (and (not (<= (* skoY (+ (* skoX (* skoX (/ 1. 6.))) (* skoY (* skoY (+ (/ (- 1.) 6.) (* skoY (* skoY (/ 1. 120.)))))))) 0.)) (and (not (<= skoX 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 2.))) (and (<= 0. skoX) (not (<= skoY skoX))))))))))
(set-info :status sat)
(check-sat)
