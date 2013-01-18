(set-logic QF_NRA)

(declare-fun pi () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (+ (* pi (* pi (* pi (* pi (/ (- 1.) 12.))))) (* skoX (+ (* pi (* pi (+ (/ 1. 2.) (* pi (* pi (/ (- 1.) 24.)))))) (* skoX (* pi (* pi (/ 1. 2.)))))))) (* pi (* pi (* pi (* pi (/ 1. 24.)))))) (and (not (<= (* skoX (+ 2. skoX)) (- 1.))) (and (= (* skoY skoY) 3.) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= 0. skoY) (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)
