(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoX (* skoX (- 3600000000.))) 3600000000000000000000000.)) (and (not (<= (* skoY (* skoY (+ (+ 1800000000000000000000000. (* skoX (* skoX 1800000000.))) (* skoY (* skoY (+ (- 150000000000000000000000.) (* skoX (* skoX (- 150000000.))))))))) (+ 3600120000000000000000000. (* skoX (* skoX 3600120000.))))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))
(set-info :status unsat)
(check-sat)
