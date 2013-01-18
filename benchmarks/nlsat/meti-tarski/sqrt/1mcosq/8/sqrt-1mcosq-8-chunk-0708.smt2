(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoY (+ 1. (* skoY (+ (* skoX (* pi (- 2.))) (* skoY (* skoY (+ (* skoX (* pi (/ 2. 3.))) (* skoY (* skoY (+ (* skoX (* pi (/ (- 1.) 12.))) (* skoY (* skoY (* skoX (* pi (/ 1. 288.))))))))))))))) 0.) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.))))))))))
(set-info :status sat)
(check-sat)
