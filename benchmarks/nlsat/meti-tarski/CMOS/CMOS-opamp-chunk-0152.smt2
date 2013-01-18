(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (* skoY (* skoX (* skoX (+ (- 1800000000000000000000000.) (* skoX (* skoX (- 1800000000.)))))))) (* skoX (* skoX (+ (- 3600000000000000000000000.) (* skoX (* skoX (- 3600000000.))))))) (and (<= (* skoY (* skoY (+ (* skoX (* skoX (+ 3600060000000000000000000. (* skoX (* skoX 3600060000.))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (- 1050000000000000000000000.) (* skoX (* skoX (- 1050000000.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ 80000000000000000000000. (* skoX (* skoX 80000000.))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 18125000000000000000000.) 7.) (* skoX (* skoX (/ (- 18125000.) 7.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 2875000000000000000000. 63.) (* skoX (* skoX (/ 2875000. 63.)))))) (* skoY (* skoY (* skoX (* skoX (+ (/ (- 31250000000000000000.) 63.) (* skoX (* skoX (/ (- 31250.) 63.))))))))))))))))))))))) (+ (- 970000000000000000000000000000.) (* skoX (* skoX (+ 120000000000000000000. (* skoX (* skoX 3600119999.))))))) (and (<= 100. skoX) (and (<= skoX 120.) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoY (* pi (/ 1. 3.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))))))
(set-info :status unsat)
(check-sat)
