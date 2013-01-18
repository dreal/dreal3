(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (+ (/ 1. 24.) (* skoX (* skoX (+ (/ (- 1.) 720.) (* skoX (* skoX (+ (/ 1. 40320.) (* skoX (* skoX (+ (/ (- 1.) 3628800.) (* skoX (* skoX (+ (/ 1. 479001600.) (* skoX (* skoX (/ (- 1.) 87178291200.))))))))))))))))))))) (- 1.)) (and (not (<= (* skoX (* skoX (+ (- 1.) (* skoX (* skoX (+ (/ 1. 3.) (* skoX (* skoX (+ (/ (- 2.) 45.) (* skoX (* skoX (+ (/ 127. 40320.) (* skoX (* skoX (+ (/ (- 233.) 1814400.) (* skoX (* skoX (+ (/ 743. 239500800.) (* skoX (* skoX (+ (/ (- 2.) 42567525.) (* skoX (* skoX (+ (/ 829. 1743565824000.) (* skoX (* skoX (+ (/ (- 53.) 15692092416000.) (* skoX (* skoX (/ 1. 62768369664000.)))))))))))))))))))))))))))))) 0.)) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))))))))))
(set-info :status unsat)
(check-sat)
