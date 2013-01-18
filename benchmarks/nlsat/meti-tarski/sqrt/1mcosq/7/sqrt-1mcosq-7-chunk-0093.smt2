(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= 0. skoY)) (and (not (<= skoY (* skoX 10.))) (and (<= (* skoY (* skoY (+ (/ (- 1.) 2.) (* skoY (* skoY (+ (/ 1. 24.) (* skoY (* skoY (/ (- 1.) 720.))))))))) (- 1.)) (and (<= (* skoY (* skoY (/ (- 1.) 2.))) (- 1.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 2.))) (and (<= (/ 1. 20.) skoX) (not (<= skoY skoX)))))))))))
(set-info :status unsat)
(check-sat)
