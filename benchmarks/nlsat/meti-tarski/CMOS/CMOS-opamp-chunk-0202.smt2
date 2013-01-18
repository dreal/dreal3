(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (* skoY (+ (* skoX (* skoX (+ (- 1800000000000000000000000.) (* skoX (* skoX (- 1800000000.)))))) (* skoY (* skoY (* skoX (* skoX (+ 150000000000000000000000. (* skoX (* skoX 150000000.)))))))))) (* skoX (* skoX (+ (- 3600000000000000000000000.) (* skoX (* skoX (- 3600000000.))))))) (and (<= (* skoY (* skoY (+ (* skoX (* skoX (+ 1800000000000000000000000. (* skoX (* skoX 1800000000.))))) (* skoY (* skoY (* skoX (* skoX (+ (- 150000000000000000000000.) (* skoX (* skoX (- 150000000.))))))))))) (* skoX (* skoX (+ 3600000000000000000000000. (* skoX (* skoX 3600000000.)))))) (and (not (<= (* skoY (* skoY (+ (* skoX (* skoX (+ (- 60000000000000000000.) (* skoX (* skoX (- 60000.)))))) (* skoY (* skoY (* skoX (* skoX (+ 5000000000000000000. (* skoX (* skoX 5000.)))))))))) (+ 970000000000000000000000000000. (* skoX (* skoX (+ 3599880000000000000000000. (* skoX (* skoX (- 119999.))))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 3.))) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoX 120.) (<= 100. skoX))))))))))
(set-info :status unsat)
(check-sat)
