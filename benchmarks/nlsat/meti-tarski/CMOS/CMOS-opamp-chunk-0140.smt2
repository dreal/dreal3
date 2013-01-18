(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (* skoX (* skoX (+ 60000000000000000000. (* skoX (* skoX 60000.))))))) (+ (- 970000000000000000000000000000.) (* skoX (* skoX (+ (- 3599880000000000000000000.) (* skoX (* skoX 119999.)))))))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))
(set-info :status sat)
(check-sat)
