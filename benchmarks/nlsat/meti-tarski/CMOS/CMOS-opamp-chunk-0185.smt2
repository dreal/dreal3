(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (* skoY (+ (* skoX (* skoX (+ 3600060000000000000000000. (* skoX (* skoX 3600060000.))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (- 1200005000000000000000000.) (* skoX (* skoX (- 1200005000.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 480000500000000000000000. 3.) (* skoX (* skoX (/ 480000500. 3.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 240000062500000000000000.) 21.) (* skoX (* skoX (/ (- 480000125.) 42.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 96000006250000000000000. 189.) (* skoX (* skoX (/ 384000025. 756.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 968750000000000000000.) 63.) (* skoX (* skoX (/ (- 968750.) 63.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 62500000000000000000. 189.) (* skoX (* skoX (/ 62500. 189.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ (- 19726562500000000000.) 3969.) (* skoX (* skoX (/ (- 315625.) 63504.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ (/ 195312500000000000. 3969.) (* skoX (* skoX (/ 3125. 63504.)))))) (* skoY (* skoY (* skoX (* skoX (+ (/ (- 9765625000000000.) 35721.) (* skoX (* skoX (/ (- 625.) 2286144.))))))))))))))))))))))))))))))))))) (+ (- 970000000000000000000000000000.) (* skoX (* skoX (+ 120000000000000000000. (* skoX (* skoX 3600119999.))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 3.))) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoX 120.) (<= 100. skoX))))))))
(set-info :status unsat)
(check-sat)
