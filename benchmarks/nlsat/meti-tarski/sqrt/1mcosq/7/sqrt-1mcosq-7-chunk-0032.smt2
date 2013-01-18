(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (* skoY (/ (- 1.) 2.))) (- 1.))) (and (not (<= skoY skoX)) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (* skoY (* skoY (/ 1. 2.))) 1.)) (not (<= (* skoY (* skoY (+ (/ 1. 2.) (* skoY (* skoY (+ (/ (- 1.) 24.) (* skoY (* skoY (/ 1. 720.))))))))) 1.))))))))
(set-info :status unsat)
(check-sat)
