(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (+ (- 1.) (* skoY (* skoY (+ (/ 1. 6.) (* skoY (* skoY (/ (- 1.) 120.)))))))) 0.)) (and (not (<= (* skoY (+ (* skoX (* skoX (/ 1. 6.))) (* skoY (* skoY (+ (/ (- 1.) 6.) (* skoY (* skoY (/ 1. 120.)))))))) 0.)) (and (not (<= skoX 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)
