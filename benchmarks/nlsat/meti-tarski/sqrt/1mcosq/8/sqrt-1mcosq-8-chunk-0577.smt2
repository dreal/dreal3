(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (* skoX (+ (- 1.) (* skoX (* skoX (+ (/ 1. 3.) (* skoX (* skoX (+ (/ (- 2.) 45.) (* skoX (* skoX (+ (/ 127. 40320.) (* skoX (* skoX (+ (/ (- 233.) 1814400.) (* skoX (* skoX (+ (/ 743. 239500800.) (* skoX (* skoX (+ (/ (- 2.) 42567525.) (* skoX (* skoX (+ (/ 829. 1743565824000.) (* skoX (* skoX (+ (/ (- 53.) 15692092416000.) (* skoX (* skoX (/ 1. 62768369664000.)))))))))))))))))))))))))))))) 0.)) (and (not (<= skoY skoX)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))
(set-info :status sat)
(check-sat)
