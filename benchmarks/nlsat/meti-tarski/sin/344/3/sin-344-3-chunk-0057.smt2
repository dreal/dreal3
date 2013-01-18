(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (+ (- 2.) (* skoX (* skoX (/ 1. 2.)))) (* skoY (+ skoX (* skoY (/ 1. 2.))))) (* skoZ (+ (+ (* skoX (/ 1. 2.)) (* skoY (/ 1. 2.))) (* skoZ (/ 1. 3.)))))) (+ (* skoX (+ 2. (* skoX (* skoX (+ (/ (- 1.) 3.) (* skoX (* skoX (+ (/ 1. 120.) (* skoX (* skoX (/ (- 1.) 5040.))))))))))) (* skoY (+ (+ 2. (* skoX (* skoX (/ (- 1.) 2.)))) (* skoY (+ (* skoX (/ (- 1.) 2.)) (* skoY (+ (/ (- 1.) 3.) (* skoY (* skoY (+ (/ 1. 120.) (* skoY (* skoY (/ (- 1.) 5040.)))))))))))))) (and (not (<= 3. skoX)) (and (not (<= 3. skoY)) (and (not (<= 3. skoZ)) (and (not (<= skoX (/ 1. 10.))) (and (not (<= skoY (/ 1. 10.))) (not (<= skoZ (/ 1. 10.))))))))))
(set-info :status sat)
(check-sat)
