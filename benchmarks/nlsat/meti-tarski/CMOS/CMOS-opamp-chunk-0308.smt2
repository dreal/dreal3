(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (+ (* skoX (* skoX (+ (- 1800030000000000000000000.) (* skoX (* skoX (- 1800030000.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ 525000000000000000000000. (* skoX (* skoX 525000000.))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (- 40000000000000000000000.) (* skoX (* skoX (- 40000000.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 9062500000000000000000. 7.) (* skoX (* skoX (/ 9062500. 7.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 1437500000000000000000.) 63.) (* skoX (* skoX (/ (- 1437500.) 63.)))))) (* skoY (* skoY (* skoX (* skoX (+ (/ 15625000000000000000. 63.) (* skoX (* skoX (/ 15625. 63.))))))))))))))))))))))) (+ (/ 55289999999999882000000000000057. 114.) (* skoX (* skoX (+ (- 60000000000000000000.) (* skoX (* skoX (/ (- 3600119999.) 2.))))))))) (and (<= 100. skoX) (and (<= skoX 120.) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoY (* pi (/ 1. 3.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))))))
(set-info :status unsat)
(check-sat)
