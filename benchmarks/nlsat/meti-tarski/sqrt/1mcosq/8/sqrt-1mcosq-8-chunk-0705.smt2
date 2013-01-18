(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (+ 1. (* skoY (+ (* skoX (* pi (- 2.))) (* skoY (* skoY (+ (* skoX (* pi (/ 2. 3.))) (* skoY (* skoY (+ (* skoX (* pi (/ (- 1.) 12.))) (* skoY (* skoY (* skoX (* pi (/ 1. 288.))))))))))))))) 0.)) (and (not (<= skoY skoX)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))
(set-info :status sat)
(check-sat)
