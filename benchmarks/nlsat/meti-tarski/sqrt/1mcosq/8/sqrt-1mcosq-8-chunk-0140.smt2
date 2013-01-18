(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (* skoY (+ 1. (* skoY (* skoY (+ (/ (- 1.) 3.) (* skoY (* skoY (+ (/ 2. 45.) (* skoY (* skoY (+ (/ (- 1.) 315.) (* skoY (* skoY (+ (/ 2. 14175.) (* skoY (* skoY (+ (/ (- 31.) 7257600.) (* skoY (* skoY (+ (/ 1. 10886400.) (* skoY (* skoY (+ (/ (- 101.) 73156608000.) (* skoY (* skoY (+ (/ 1. 73156608000.) (* skoY (* skoY (/ (- 1.) 13168189440000.)))))))))))))))))))))))))))))) 0.)) (and (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= (/ 1. 10.) skoX) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
