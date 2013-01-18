(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (* skoY (+ (- 1.) (* skoY (* skoY (+ (/ 7. 24.) (* skoY (* skoY (+ (/ (- 1.) 45.) (* skoY (* skoY (+ (/ 29. 40320.) (* skoY (* skoY (+ (/ (- 23.) 1814400.) (* skoY (* skoY (+ (/ 67. 479001600.) (* skoY (* skoY (+ (/ (- 23.) 21794572800.) (* skoY (* skoY (/ 1. 174356582400.)))))))))))))))))))))))) 0.)) (and (not (<= (* skoY (* skoY (+ (/ 1. 2.) (* skoY (* skoY (+ (/ (- 1.) 24.) (* skoY (* skoY (+ (/ 1. 720.) (* skoY (* skoY (+ (/ (- 1.) 40320.) (* skoY (* skoY (+ (/ 1. 3628800.) (* skoY (* skoY (+ (/ (- 1.) 479001600.) (* skoY (* skoY (/ 1. 87178291200.))))))))))))))))))))) 1.)) (and (not (<= skoY skoX)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))))
(set-info :status sat)
(check-sat)
