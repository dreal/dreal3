(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (and (<= (* skoZ (+ (+ (- 9.) (* skoX (* skoX (- 3.)))) (* skoY (+ (* skoX (+ 9. (* skoX (* skoX 3.)))) (* skoY (+ (+ (- 3.) (* skoX (* skoX (- 1.)))) (* skoY (* skoX (+ 3. (* skoX skoX)))))))))) (+ (+ (/ 9. 4.) (* skoX (* skoX (+ (/ 3. 4.) (* skoX 3.))))) (* skoY (+ (* skoX (+ (/ (- 9.) 4.) (* skoX (+ 9. (* skoX (/ (- 3.) 4.)))))) (* skoY (+ (+ (/ 3. 4.) (* skoX (+ 9. (* skoX (+ (/ 1. 4.) (* skoX 4.)))))) (* skoY (+ 3. (* skoX (+ (/ (- 3.) 4.) (* skoX (+ 4. (* skoX (/ (- 1.) 4.)))))))))))))) (and (not (<= 0. skoY)) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))
(set-info :status sat)
(check-sat)
