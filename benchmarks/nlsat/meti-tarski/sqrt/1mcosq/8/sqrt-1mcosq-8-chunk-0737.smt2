(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoX (* skoX (/ (- 1.) 4.))) (/ (- 1.) 2.))) (and (not (<= (* skoY (+ (* skoX (* pi (- 2.))) (* skoY (* skoY (+ (* skoX (* pi (/ 2. 3.))) (* skoY (* skoY (+ (* skoX (* pi (/ (- 1.) 12.))) (* skoY (* skoY (* skoX (* pi (/ 1. 288.))))))))))))) (+ (/ (- 1.) 2.) (* skoX (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (/ 1. 8.))))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
