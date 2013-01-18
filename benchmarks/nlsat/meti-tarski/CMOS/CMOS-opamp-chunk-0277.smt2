(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (* skoY (* skoX (* skoX (+ (- 900000000000000000000000.) (* skoX (* skoX (- 900000000.)))))))) (* skoX (* skoX (+ (- 1800000000000000000000000.) (* skoX (* skoX (- 1800000000.))))))) (and (<= (* skoY (* skoY (* skoX (* skoX (+ (- 30000000000000000000.) (* skoX (* skoX (- 30000.)))))))) (+ (/ 55289999999999882000000000000057. 114.) (* skoX (* skoX (+ 1799940000000000000000000. (* skoX (* skoX (/ (- 119999.) 2.)))))))) (and (<= (* skoY (* skoY (* skoX (* skoX (+ 900000000000000000000000. (* skoX (* skoX 900000000.))))))) (* skoX (* skoX (+ 1800000000000000000000000. (* skoX (* skoX 1800000000.)))))) (and (<= 100. skoX) (and (<= skoX 120.) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoY (* pi (/ 1. 3.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))))))))
(set-info :status unsat)
(check-sat)
