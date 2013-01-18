(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (* skoX (+ (/ 1. 2.) (* skoX (* skoX (+ (/ (- 1.) 24.) (* skoX (* skoX (+ (/ 1. 720.) (* skoX (* skoX (+ (/ (- 1.) 40320.) (* skoX (* skoX (+ (/ 1. 3628800.) (* skoX (* skoX (+ (/ (- 1.) 479001600.) (* skoX (* skoX (+ (/ 1. 87178291200.) (* skoX (* skoX (/ (- 1.) 20922789888000.)))))))))))))))))))))))) 1.)) (and (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= (/ 1. 10.) skoX) (not (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)
