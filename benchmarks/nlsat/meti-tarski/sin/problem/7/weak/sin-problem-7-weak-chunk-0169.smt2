(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= skoY (* skoX 2000.)) (and (not (<= (* skoY (+ (/ (- 1.) 2000.) (* skoY (+ (* skoX (/ (- 1.) 6.)) (* skoY (+ (/ 1. 12000.) (* skoY (+ (* skoX (/ 1. 120.)) (* skoY (/ (- 1.) 240000.)))))))))) (* skoX (* skoX (* skoX (+ (/ (- 1.) 6.) (* skoX (* skoX (+ (/ 1. 120.) (* skoX (* skoX (/ (- 1.) 5040.)))))))))))) (and (not (<= (* skoY (+ (* skoX (* skoX (* skoX (/ 1. 6.)))) (* skoY (+ (/ (- 1.) 2000.) (* skoY (+ (* skoX (/ (- 1.) 6.)) (* skoY (+ (/ 1. 12000.) (* skoY (+ (* skoX (/ 1. 120.)) (* skoY (/ (- 1.) 240000.)))))))))))) 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= (* pi (/ 1. 2.)) skoY)) (and (not (<= skoX 0.)) (and (not (<= skoY skoX)) (and (or (not (<= (* skoX 2000.) skoY)) (not (<= skoY (* skoX 2000.)))) (and (or (not (<= (* skoX (* skoX (* skoX (/ 1000. 3.)))) skoY)) (<= (* skoX 2000.) skoY)) (<= skoY (* skoX 2000.)))))))))))))
(set-info :status sat)
(check-sat)
