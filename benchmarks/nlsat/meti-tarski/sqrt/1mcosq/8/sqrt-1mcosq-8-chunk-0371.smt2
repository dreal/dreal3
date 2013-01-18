(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoY (* skoY (+ 1. (* skoY (* skoY (+ (/ (- 1.) 3.) (* skoY (* skoY (+ (/ 2. 45.) (* skoY (* skoY (+ (/ (- 127.) 40320.) (* skoY (* skoY (+ (/ 233. 1814400.) (* skoY (* skoY (+ (/ (- 1.) 322560.) (* skoY (* skoY (+ (/ 1. 21772800.) (* skoY (* skoY (/ (- 1.) 2612736000.)))))))))))))))))))))))) 0.) (and (not (<= (* skoY (* skoY (+ (/ 1. 2.) (* skoY (* skoY (+ (/ (- 1.) 24.) (* skoY (* skoY (+ (/ 1. 720.) (* skoY (* skoY (+ (/ (- 1.) 40320.) (* skoY (* skoY (/ 1. 3628800.))))))))))))))) 1.)) (and (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= (/ 1. 10.) skoX) (not (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
