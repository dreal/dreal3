(set-logic QF_NRA)

(declare-fun pi () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (* pi (/ (- 1.) 2.))) 0.)) (and (not (<= (+ (/ (- 1.) 2000.) (* pi (/ 1. 2.))) skoY)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= skoX 0.)) (not (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)
