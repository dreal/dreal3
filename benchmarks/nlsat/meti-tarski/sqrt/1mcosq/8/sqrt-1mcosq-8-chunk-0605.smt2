(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (+ (/ 1. 24.) (* skoX (* skoX (+ (/ (- 1.) 720.) (* skoX (* skoX (+ (/ 1. 40320.) (* skoX (* skoX (/ (- 1.) 3628800.))))))))))))))) (- 1.)) (and (not (<= (* skoX (* skoX (+ (- 1.) (* skoX (* skoX (+ (/ 1. 3.) (* skoX (* skoX (+ (/ (- 2.) 45.) (* skoX (* skoX (+ (/ 1. 315.) (* skoX (* skoX (+ (/ (- 2.) 14175.) (* skoX (* skoX (+ (/ 31. 7257600.) (* skoX (* skoX (+ (/ (- 1.) 10886400.) (* skoX (* skoX (+ (/ 101. 73156608000.) (* skoX (* skoX (+ (/ (- 1.) 73156608000.) (* skoX (* skoX (/ 1. 13168189440000.)))))))))))))))))))))))))))))) 0.)) (and (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= (/ 1. 10.) skoX) (not (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
