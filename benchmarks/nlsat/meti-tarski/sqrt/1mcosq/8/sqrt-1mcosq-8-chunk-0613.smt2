(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (* skoX (+ (- 1.) (* skoX (* skoX (+ (/ 1. 3.) (* skoX (* skoX (+ (/ (- 2.) 45.) (* skoX (* skoX (+ (/ 1. 315.) (* skoX (* skoX (+ (/ (- 2.) 14175.) (* skoX (* skoX (+ (/ 2047. 479001600.) (* skoX (* skoX (+ (/ (- 1.) 10762752.) (* skoX (* skoX (+ (/ 15413. 10461394944000.) (* skoX (* skoX (+ (/ (- 107.) 6276836966400.) (* skoX (* skoX (+ (/ 541. 3766102179840000.) (* skoX (* skoX (+ (/ (- 17.) 19772036444160000.) (* skoX (* skoX (/ 1. 316352583106560000.)))))))))))))))))))))))))))))))))))) 0.)) (and (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= (/ 1. 10.) skoX) (not (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)
