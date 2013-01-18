(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (* skoY (+ (/ (- 1.) 2.) (* skoY (* skoY (+ (/ 1. 24.) (* skoY (* skoY (+ (/ (- 1.) 720.) (* skoY (* skoY (+ (/ 1. 40320.) (* skoY (* skoY (+ (/ (- 1.) 3628800.) (* skoY (* skoY (+ (/ 1. 479001600.) (* skoY (* skoY (/ (- 1.) 87178291200.))))))))))))))))))))) (- 1.))) (and (not (<= (* skoY (* skoY (+ 1. (* skoY (* skoY (+ (/ (- 1.) 3.) (* skoY (* skoY (+ (/ 2. 45.) (* skoY (* skoY (+ (/ (- 127.) 40320.) (* skoY (* skoY (+ (/ 233. 1814400.) (* skoY (* skoY (+ (/ (- 743.) 239500800.) (* skoY (* skoY (+ (/ 2. 42567525.) (* skoY (* skoY (+ (/ (- 829.) 1743565824000.) (* skoY (* skoY (+ (/ 53. 15692092416000.) (* skoY (* skoY (/ (- 1.) 62768369664000.)))))))))))))))))))))))))))))) 0.)) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))))))))))
(set-info :status sat)
(check-sat)
