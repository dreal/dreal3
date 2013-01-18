(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ 3. (* skoX (/ 399. 50.))) (* skoY (+ (+ (/ 399. 50.) (* skoX (* skoX (/ (- 399.) 50.)))) (* skoY (+ (+ 6. (* skoX (+ (/ (- 399.) 50.) (* skoX (- 3.))))) (* skoY (* skoX (- 6.)))))))) (* skoZ (+ (/ 399. 100.) (* skoY (+ (+ 3. (* skoX (/ (- 399.) 50.))) (* skoY (+ (* skoX (+ (- 6.) (* skoX (/ 399. 100.)))) (* skoY (* skoX (* skoX 3.))))))))))) (+ (+ (/ (- 133.) 100.) (* skoX (+ (- 3.) (* skoX (/ (- 399.) 100.))))) (* skoY (+ (+ (- 4.) (* skoX (/ (- 133.) 25.))) (* skoY (+ (+ (/ (- 399.) 100.) (* skoX (+ (- 1.) (* skoX (/ (- 133.) 100.))))) (* skoY (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
