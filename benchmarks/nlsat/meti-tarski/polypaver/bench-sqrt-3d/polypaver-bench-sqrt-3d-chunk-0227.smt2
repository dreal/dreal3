(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (* skoY (+ (* skoX (/ 1. 4.)) (* skoY (+ (* skoX (/ 1. 2.)) (* skoY (* skoX (/ 1. 4.))))))) (* skoZ (* skoY (* skoY (+ (* skoX (+ (- 4.) (* skoX (/ 1. 4.)))) (* skoY (+ (* skoX (* skoX (/ 1. 2.))) (* skoY (* skoX (* skoX (/ 1. 4.)))))))))))) (+ (/ (- 1.) 16.) (* skoY (+ (/ (- 1.) 8.) (* skoY (/ (- 1.) 16.)))))) (and (<= skoZ 1.) (and (or (not (<= (* skoZ (* skoY (+ (* skoX (+ (/ (- 7.) 2.) (* skoX (/ 1. 2.)))) (* skoY (* skoX (+ (/ 1. 2.) (* skoX (/ 1. 2.)))))))) (+ (+ (/ (- 1.) 4.) (* skoX (/ (- 1.) 4.))) (* skoY (+ (/ (- 1.) 4.) (* skoX (/ (- 1.) 4.))))))) (not (<= skoZ 1.))) (and (or (not (<= skoX 1.)) (not (<= skoZ 1.))) (and (<= 1. skoX) (and (<= 1. skoY) (and (<= 1. skoZ) (and (<= skoX 2.) (and (<= skoY 2.) (and (<= skoZ 2.) (and (or (not (<= skoX 1.)) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))))))))))))))
(set-info :status sat)
(check-sat)
