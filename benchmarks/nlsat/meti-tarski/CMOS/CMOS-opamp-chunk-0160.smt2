(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (+ (* skoX (* skoX (+ 60000000000000000000. (* skoX (* skoX 60000.))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (- 5000000000000000000.) (* skoX (* skoX (- 5000.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 500000000000000000. 3.) (* skoX (* skoX (/ 500. 3.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 62500000000000000.) 21.) (* skoX (* skoX (/ (- 125.) 42.)))))) (* skoY (* skoY (* skoX (* skoX (+ (/ 6250000000000000. 189.) (* skoX (* skoX (/ 25. 756.)))))))))))))))))))) (+ (- 970000000000000000000000000000.) (* skoX (* skoX (+ (- 3599880000000000000000000.) (* skoX (* skoX 119999.)))))))) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (/ 31415927. 10000000.) pi)))))
(set-info :status sat)
(check-sat)
