(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (* skoX (+ 1800000000000000000000000. (* skoX (* skoX 1800000000.))))) 0.) (and (not (<= (* skoX (* skoX (+ 60000000000000000000. (* skoX (* skoX 60000.))))) 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= skoY (* pi (/ 1. 3.))) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoX 120.) (<= 100. skoX)))))))))
(set-info :status unsat)
(check-sat)
