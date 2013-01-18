(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoX (* skoX 1800000000.)) (- 1800000000000000000000000.)) (and (<= (* skoY (* skoY (+ (+ (- 900000000000000000000000.) (* skoX (* skoX (- 900000000.)))) (* skoY (* skoY (+ (+ 75000000000000000000000. (* skoX (* skoX 75000000.))) (* skoY (* skoY (+ (+ (- 2500000000000000000000.) (* skoX (* skoX (- 2500000.)))) (* skoY (* skoY (+ (+ (/ 312500000000000000000. 7.) (* skoX (* skoX (/ 312500. 7.)))) (* skoY (* skoY (+ (+ (/ (- 31250000000000000000.) 63.) (* skoX (* skoX (/ (- 31250.) 63.)))) (* skoY (* skoY (+ (/ 7812500000000000000. 2079.) (* skoX (* skoX (/ 15625. 4158.))))))))))))))))))))) (+ (- 1800060000000000000000000.) (* skoX (* skoX (- 1800060000.))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 3.))) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoX 120.) (<= 100. skoX)))))))))
(set-info :status unsat)
(check-sat)
