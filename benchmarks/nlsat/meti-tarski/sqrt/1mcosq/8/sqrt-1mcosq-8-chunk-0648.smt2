(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (* skoY (+ (/ 1. 2.) (* skoY (* skoY (+ (/ (- 1.) 24.) (* skoY (* skoY (+ (/ 1. 720.) (* skoY (* skoY (+ (/ (- 1.) 40320.) (* skoY (* skoY (+ (/ 1. 3628800.) (* skoY (* skoY (+ (/ (- 1.) 479001600.) (* skoY (* skoY (+ (/ 1. 87178291200.) (* skoY (* skoY (+ (/ (- 1.) 20922789888000.) (* skoY (* skoY (+ (/ 1. 6402373705728000.) (* skoY (* skoY (+ (/ (- 1.) 2432902008176640000.) (* skoY (* skoY (/ 1. 1124000727777607680000.))))))))))))))))))))))))))))))))) 1.)) (and (not (<= skoY skoX)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))
(set-info :status sat)
(check-sat)
