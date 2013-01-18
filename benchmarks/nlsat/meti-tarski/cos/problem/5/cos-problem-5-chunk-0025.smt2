(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (+ (- 1.) (* skoX (+ (- 2.) (* skoX (- 1.)))))) 0.) (and (<= (* skoX (+ 1. (* skoX (+ 2. skoX)))) 0.) (and (<= (* skoX (+ (+ 1. (* pi (* pi (/ (- 1.) 2.)))) (* skoX (+ 2. skoX)))) (* pi (* pi (/ 1. 2.)))) (and (= (* skoY skoY) 3.) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= 0. skoY) (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
