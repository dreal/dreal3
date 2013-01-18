(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (+ (* skoX (* skoX (+ (- 60000000000000000000.) (* skoX (* skoX (- 60000.)))))) (* skoY (* skoY (* skoX (* skoX (+ 5000000000000000000. (* skoX (* skoX 5000.)))))))))) (+ 970000000000000000000000000000. (* skoX (* skoX (+ 3599880000000000000000000. (* skoX (* skoX (- 119999.))))))))) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (/ 31415927. 10000000.) pi)))))
(set-info :status sat)
(check-sat)
