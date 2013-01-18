(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= skoY skoX)) (and (not (<= (* skoX (* skoX (/ 1. 2.))) 1.)) (and (not (<= (* skoX (* skoX (+ (/ 1. 2.) (* skoX (* skoX (+ (/ (- 1.) 24.) (* skoX (* skoX (/ 1. 720.))))))))) 1.)) (and (not (<= (* skoX (* skoX (+ (/ 1. 2.) (* skoX (* skoX (+ (/ (- 1.) 24.) (* skoX (* skoX (+ (/ 1. 720.) (* skoX (* skoX (+ (/ (- 1.) 40320.) (* skoX (* skoX (/ 1. 3628800.))))))))))))))) 1.)) (not (<= (* skoX (* skoX (+ (/ 1. 2.) (* skoX (* skoX (+ (/ (- 1.) 24.) (* skoX (* skoX (+ (/ 1. 720.) (* skoX (* skoX (+ (/ (- 1.) 40320.) (* skoX (* skoX (+ (/ 1. 3628800.) (* skoX (* skoX (+ (/ (- 1.) 479001600.) (* skoX (* skoX (/ 1. 87178291200.))))))))))))))))))))) 1.)))))))))
(set-info :status sat)
(check-sat)
