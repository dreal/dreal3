(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (+ (/ 1. 24.) (* skoX (* skoX (/ (- 1.) 720.))))))))) (- 1.)) (and (not (<= (* skoX (* skoX (+ (- 1.) (* skoX (* skoX (+ (/ 1. 3.) (* skoX (* skoX (+ (/ (- 2.) 45.) (* skoX (* skoX (+ (/ 127. 40320.) (* skoX (* skoX (+ (/ (- 233.) 1814400.) (* skoX (* skoX (+ (/ 1. 322560.) (* skoX (* skoX (+ (/ (- 1.) 21772800.) (* skoX (* skoX (/ 1. 2612736000.)))))))))))))))))))))))) 0.)) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))))))))))
(set-info :status unsat)
(check-sat)
