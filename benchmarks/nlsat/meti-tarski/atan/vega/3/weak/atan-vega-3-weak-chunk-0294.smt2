(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (- 3.) (* skoX (/ (- 1.) 2.))) (* skoY (+ (+ (/ (- 1.) 2.) (* skoX (+ 8. (* skoX (/ 1. 2.))))) (* skoY (+ (+ 2. (* skoX (+ (/ 1. 2.) (* skoX (- 5.))))) (* skoY (* skoX (- 2.)))))))) (* skoZ (+ (/ (- 1.) 4.) (* skoY (+ (+ 1. (* skoX (/ 1. 2.))) (* skoY (+ (* skoX (+ (- 2.) (* skoX (/ (- 1.) 4.)))) (* skoY (* skoX skoX)))))))))) (+ (+ (/ 3. 4.) (* skoX (+ 3. (* skoX (/ 1. 4.))))) (* skoY (+ (* skoX (+ (- 1.) (* skoX (- 4.)))) (* skoY (+ (+ (/ 1. 4.) (* skoX (+ 1. (* skoX (/ 3. 4.))))) (* skoY (+ (- 1.) (* skoX (* skoX (- 3.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
