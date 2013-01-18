(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (* skoY (+ (* skoX (* skoX (+ 3600060000000000000000000. (* skoX (* skoX 3600060000.))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (- 1050005000000000000000000.) (* skoX (* skoX (- 1050005000.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 240000500000000000000000. 3.) (* skoX (* skoX (/ 240000500. 3.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 54375062500000000000000.) 21.) (* skoX (* skoX (/ (- 108750125.) 42.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 1232143750000000000000. 27.) (* skoX (* skoX (/ 4928575. 108.)))))) (* skoY (* skoY (* skoX (* skoX (+ (/ (- 31250000000000000000.) 63.) (* skoX (* skoX (/ (- 31250.) 63.))))))))))))))))))))))) (+ (- 970000000000000000000000000000.) (* skoX (* skoX (+ 120000000000000000000. (* skoX (* skoX 3600119999.))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 3.))) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoX 120.) (<= 100. skoX))))))))
(set-info :status unsat)
(check-sat)
