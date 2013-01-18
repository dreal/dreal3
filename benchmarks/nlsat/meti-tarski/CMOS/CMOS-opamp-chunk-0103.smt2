(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (+ (* skoX (* skoX (+ (- 3600060000000000000000000.) (* skoX (* skoX (- 3600060000.)))))) (* skoY (* skoY (* skoX (* skoX (+ 900000000000000000000000. (* skoX (* skoX 900000000.)))))))))) (+ 970000000000000000000000000000. (* skoX (* skoX (+ (- 120000000000000000000.) (* skoX (* skoX (- 3600119999.))))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 3.))) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoX 120.) (<= 100. skoX))))))))
(set-info :status unsat)
(check-sat)
