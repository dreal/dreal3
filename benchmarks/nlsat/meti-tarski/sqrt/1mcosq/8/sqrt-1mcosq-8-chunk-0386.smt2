(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoY (* skoY (+ (- 1.) (* skoY (* skoY (+ (/ 1. 3.) (* skoY (* skoY (+ (/ (- 2.) 45.) (* skoY (* skoY (+ (/ 1. 315.) (* skoY (* skoY (+ (/ (- 2.) 14175.) (* skoY (* skoY (+ (/ 2047. 479001600.) (* skoY (* skoY (+ (/ (- 1.) 10762752.) (* skoY (* skoY (+ (/ 15413. 10461394944000.) (* skoY (* skoY (+ (/ (- 107.) 6276836966400.) (* skoY (* skoY (+ (/ 541. 3766102179840000.) (* skoY (* skoY (+ (/ (- 17.) 19772036444160000.) (* skoY (* skoY (/ 1. 316352583106560000.)))))))))))))))))))))))))))))))))))) 0.) (and (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= (/ 1. 10.) skoX) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
