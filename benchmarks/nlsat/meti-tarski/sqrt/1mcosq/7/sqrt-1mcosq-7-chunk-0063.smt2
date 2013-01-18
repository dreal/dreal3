(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoY (* skoY (+ 1. (* skoY (* skoY (+ (/ (- 1.) 3.) (* skoY (* skoY (+ (/ 1. 24.) (* skoY (* skoY (/ (- 1.) 576.)))))))))))) 0.) (and (not (<= (* skoY (* skoY (+ (/ (- 1.) 2.) (* skoY (* skoY (/ 1. 24.)))))) (- 1.))) (and (not (<= skoY skoX)) (and (<= (/ 1. 20.) skoX) (and (<= skoY (* pi (/ 1. 2.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))))))
(set-info :status unsat)
(check-sat)
