(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoY (+ 1. (* skoY (* skoY (+ (/ (- 1.) 6.) (* skoY (* skoY (+ (/ 1. 120.) (* skoY (* skoY (+ (/ (- 1.) 5040.) (* skoY (* skoY (/ 1. 362880.)))))))))))))) 0.) (and (not (<= (* skoY (+ (+ 1. (* pi (/ (- 1.) 2.))) (* skoY (* skoY (* pi (/ 1. 12.)))))) 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= (* pi (/ 1. 2.)) skoY)) (and (not (<= skoX 0.)) (not (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
