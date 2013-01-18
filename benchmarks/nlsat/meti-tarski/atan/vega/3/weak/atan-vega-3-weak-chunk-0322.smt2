(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= (* skoX skoX) (- 3.))) (and (not (<= (* skoZ (+ (+ (+ (- 9.) (* skoX (+ (/ (- 3.) 2.) (* skoX (+ 3. (* skoX (/ (- 1.) 2.))))))) (* skoY (+ (+ (/ (- 3.) 2.) (* skoX (+ 30. (* skoX (+ 1. (* skoX (+ 2. (* skoX (/ 1. 2.))))))))) (* skoY (+ (+ 6. (* skoX (+ (/ 3. 2.) (* skoX (+ (- 19.) (* skoX (+ (/ 1. 2.) (* skoX (- 5.))))))))) (* skoY (* skoX (+ (- 6.) (* skoX (* skoX (- 2.))))))))))) (* skoZ (+ (+ (/ (- 3.) 4.) (* skoX (+ 3. (* skoX (/ (- 1.) 4.))))) (* skoY (+ (+ 3. (* skoX (+ (/ 3. 2.) (* skoX (+ (- 5.) (* skoX (/ 1. 2.))))))) (* skoY (+ (* skoX (+ (- 6.) (* skoX (+ (/ (- 3.) 4.) (* skoX (+ 1. (* skoX (/ (- 1.) 4.)))))))) (* skoY (* skoX (* skoX (+ 3. (* skoX skoX))))))))))))) (+ (+ (/ 9. 4.) (* skoX (* skoX (+ (/ 3. 2.) (* skoX (* skoX (/ 1. 4.))))))) (* skoY (+ (* skoX (+ (- 3.) (* skoX (* skoX (+ (- 1.) (* skoX (- 4.))))))) (* skoY (+ (+ (/ 3. 4.) (* skoX (* skoX (+ (/ 5. 2.) (* skoX (+ (- 8.) (* skoX (/ 3. 4.)))))))) (* skoY (+ (- 3.) (* skoX (* skoX (+ (- 10.) (* skoX (* skoX (- 3.))))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
