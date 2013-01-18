(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoX (* skoX (- 3600000000.))) 3600000000000000000000000.)) (and (not (<= (* skoY (* skoY (+ (- 1800000000000000000000000.) (* skoX (* skoX (- 1800000000.)))))) (+ (- 3600120000000000000000000.) (* skoX (* skoX (- 3600120000.)))))) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (/ 31415927. 10000000.) pi))))))
(set-info :status unsat)
(check-sat)
