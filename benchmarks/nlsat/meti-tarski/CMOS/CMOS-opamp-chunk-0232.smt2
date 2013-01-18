(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoX (* skoX (- 1800000000.))) 1800000000000000000000000.)) (and (not (<= (* skoY (* skoY (+ (+ 900000000000000000000000. (* skoX (* skoX 900000000.))) (* skoY (* skoY (+ (- 75000000000000000000000.) (* skoX (* skoX (- 75000000.))))))))) (+ 1800060000000000000000000. (* skoX (* skoX 1800060000.))))) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (/ 31415927. 10000000.) pi))))))
(set-info :status unsat)
(check-sat)
