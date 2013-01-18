(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (+ 1. (* skoY (+ (* skoX (* pi (- 2.))) (* skoY (* skoY (+ (* skoX (* pi (/ 2. 3.))) (* skoY (* skoY (+ (* skoX (* pi (/ (- 31.) 360.))) (* skoY (* skoY (+ (* skoX (* pi (/ 11. 2240.))) (* skoY (* skoY (+ (* skoX (* pi (/ (- 17.) 120960.))) (* skoY (* skoY (* skoX (* pi (/ 1. 483840.))))))))))))))))))))) 0.)) (and (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= (/ 1. 10.) skoX) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
