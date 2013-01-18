(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (* skoX (+ (- 1.) (* skoX (* skoX (+ (/ 7. 24.) (* skoX (* skoX (+ (/ (- 1.) 45.) (* skoX (* skoX (+ (/ 29. 40320.) (* skoX (* skoX (+ (/ (- 23.) 1814400.) (* skoX (* skoX (+ (/ 67. 479001600.) (* skoX (* skoX (+ (/ (- 23.) 21794572800.) (* skoX (* skoX (+ (/ 11. 1902071808000.) (* skoX (* skoX (+ (/ (- 1.) 41573855232000.) (* skoX (* skoX (+ (/ 191. 2432902008176640000.) (* skoX (* skoX (+ (/ (- 29.) 140500090972200960000.) (* skoX (* skoX (/ 1. 2248001455555215360000.)))))))))))))))))))))))))))))))))))) 0.) (and (not (<= (* skoX (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (+ (/ 1. 24.) (* skoX (* skoX (+ (/ (- 1.) 720.) (* skoX (* skoX (+ (/ 1. 40320.) (* skoX (* skoX (+ (/ (- 1.) 3628800.) (* skoX (* skoX (+ (/ 1. 479001600.) (* skoX (* skoX (+ (/ (- 1.) 87178291200.) (* skoX (* skoX (+ (/ 1. 20922789888000.) (* skoX (* skoX (+ (/ (- 1.) 6402373705728000.) (* skoX (* skoX (+ (/ 1. 2432902008176640000.) (* skoX (* skoX (/ (- 1.) 1124000727777607680000.))))))))))))))))))))))))))))))))) (- 1.))) (and (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= (/ 1. 10.) skoX) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
