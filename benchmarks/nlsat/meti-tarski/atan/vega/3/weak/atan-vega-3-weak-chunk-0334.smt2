(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoY)) (and (not (<= (* skoZ (+ (+ (+ (- 9.) (* skoX (/ (- 3.) 2.))) (* skoY (+ (+ (/ (- 3.) 2.) (* skoX (+ 24. (* skoX (/ 3. 2.))))) (* skoY (+ (+ 3. (* skoX (+ 1. (* skoX (- 15.))))) (* skoY (+ (+ (/ (- 1.) 2.) (* skoX (* skoX (/ 1. 2.)))) (* skoY (* skoX (+ (/ 1. 2.) (* skoX (- 3.)))))))))))) (* skoZ (+ (/ (- 3.) 4.) (* skoY (+ (+ 3. (* skoX (/ 3. 2.))) (* skoY (+ (+ (/ (- 1.) 4.) (* skoX (+ (- 6.) (* skoX (/ (- 3.) 4.))))) (* skoY (+ (* skoX (+ (/ 1. 2.) (* skoX 3.))) (* skoY (* skoX (* skoX (/ (- 1.) 4.)))))))))))))) (+ (+ (/ 9. 4.) (* skoX (+ 9. (* skoX (/ 3. 4.))))) (* skoY (+ (* skoX (+ (- 3.) (* skoX (- 12.)))) (* skoY (+ (+ (/ 3. 2.) (* skoX (+ 6. (* skoX (/ 5. 2.))))) (* skoY (+ (* skoX (+ (- 1.) (* skoX (- 12.)))) (* skoY (+ (/ 1. 4.) (* skoX (+ (- 3.) (* skoX (/ 3. 4.))))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
