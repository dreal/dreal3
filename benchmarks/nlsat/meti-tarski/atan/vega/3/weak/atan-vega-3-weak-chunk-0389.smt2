(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoY)) (and (not (<= (* skoZ (+ (+ (+ 9. (* skoX (/ 1197. 50.))) (* skoY (+ (+ (/ 1197. 50.) (* skoX (* skoX (/ (- 1197.) 50.)))) (* skoY (+ (+ 21. (* skoX (+ (/ (- 399.) 25.) (* skoX (- 9.))))) (* skoY (+ (+ (/ 399. 50.) (* skoX (+ (- 24.) (* skoX (/ (- 399.) 50.))))) (* skoY (* skoX (+ (/ (- 399.) 50.) (* skoX 3.))))))))))) (* skoZ (+ (/ 1197. 100.) (* skoY (+ (+ 9. (* skoX (/ (- 1197.) 50.))) (* skoY (+ (+ (/ 399. 100.) (* skoX (+ (- 18.) (* skoX (/ 1197. 100.))))) (* skoY (+ (* skoX (+ (/ (- 399.) 50.) (* skoX 9.))) (* skoY (* skoX (* skoX (/ 399. 100.)))))))))))))) (+ (+ (/ (- 399.) 100.) (* skoX (+ (- 9.) (* skoX (/ (- 1197.) 100.))))) (* skoY (+ (+ (- 12.) (* skoX (/ (- 399.) 25.))) (* skoY (+ (+ (/ (- 133.) 10.) (* skoX (+ (- 6.) (* skoX (/ (- 399.) 50.))))) (* skoY (+ (+ (- 12.) (* skoX (/ (- 133.) 25.))) (* skoY (+ (/ (- 399.) 100.) (* skoX (+ 3. (* skoX (/ (- 133.) 100.))))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
