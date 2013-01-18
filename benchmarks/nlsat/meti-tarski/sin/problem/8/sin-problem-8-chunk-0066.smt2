(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (* skoX (* pi (/ 1. 12.))))) (* skoX (+ (+ (- 1.) (* pi (/ 1. 2.))) (* skoX (* skoX (+ (/ 1. 6.) (* skoX (* skoX (+ (/ (- 1.) 120.) (* skoX (* skoX (+ (/ 1. 5040.) (* skoX (* skoX (/ (- 1.) 362880.)))))))))))))))) (and (not (<= (* skoY (+ (+ 1. (* pi (/ (- 1.) 2.))) (* skoY (* skoY (* pi (/ 1. 12.)))))) 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= (* pi (/ 1. 2.)) skoY)) (and (not (<= skoX 0.)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
