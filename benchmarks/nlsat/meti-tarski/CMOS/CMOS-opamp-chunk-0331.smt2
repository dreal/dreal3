(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (* skoY (+ (* skoX (* skoX (+ 900000000000000000000000. (* skoX (* skoX 900000000.))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (- 75000000000000000000000.) (* skoX (* skoX (- 75000000.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ 2500000000000000000000. (* skoX (* skoX 2500000.))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 312500000000000000000.) 7.) (* skoX (* skoX (/ (- 312500.) 7.)))))) (* skoY (* skoY (* skoX (* skoX (+ (/ 31250000000000000000. 63.) (* skoX (* skoX (/ 31250. 63.)))))))))))))))))))) (* skoX (* skoX (+ 1800000000000000000000000. (* skoX (* skoX 1800000000.)))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 3.))) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoX 120.) (<= 100. skoX))))))))
(set-info :status sat)
(check-sat)
