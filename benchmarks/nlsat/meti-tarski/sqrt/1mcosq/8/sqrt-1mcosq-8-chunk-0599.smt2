(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (* skoX (+ (- 1.) (* skoX (* skoX (+ (/ 1. 3.) (* skoX (* skoX (+ (/ (- 2.) 45.) (* skoX (* skoX (+ (/ 127. 40320.) (* skoX (* skoX (+ (/ (- 233.) 1814400.) (* skoX (* skoX (+ (/ 1. 322560.) (* skoX (* skoX (+ (/ (- 1.) 21772800.) (* skoX (* skoX (/ 1. 2612736000.)))))))))))))))))))))))) 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= skoY skoX))))))
(set-info :status sat)
(check-sat)
