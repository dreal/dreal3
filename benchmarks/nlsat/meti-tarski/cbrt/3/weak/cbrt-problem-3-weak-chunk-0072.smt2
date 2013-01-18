(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (/ (- 88.) 3.) (* skoX (+ 12. (* skoX (/ 1. 3.))))) (* skoY (+ (+ (/ (- 761.) 3.) (* skoX (+ (/ (- 16.) 3.) (* skoX (/ 2. 3.))))) (* skoY (+ (+ (/ (- 17.) 3.) (* skoX (/ 4. 3.))) (* skoY (/ 2. 3.))))))) (* skoZ (+ (+ (+ (/ 71. 6.) (* skoX (/ 2. 3.))) (* skoY (+ (+ (/ (- 17.) 3.) (* skoX (/ 4. 3.))) (* skoY (/ 4. 3.))))) (* skoZ (+ (/ 1. 3.) (* skoY (/ 2. 3.)))))))) (+ (+ (/ (- 80.) 3.) (* skoX (+ (/ (- 40.) 3.) (* skoX (/ (- 1.) 6.))))) (* skoY (+ (+ (/ 88. 3.) (* skoX (+ (- 12.) (* skoX (/ (- 1.) 3.))))) (* skoY (+ (+ (/ (- 71.) 6.) (* skoX (/ (- 2.) 3.))) (* skoY (/ (- 1.) 3.))))))))) (and (not (<= skoZ (/ 1. 20.))) (and (not (<= skoY (/ 1. 20.))) (and (not (<= skoX (/ 1. 20.))) (and (not (<= 15. skoZ)) (and (not (<= 15. skoY)) (not (<= 15. skoX)))))))))
(set-info :status sat)
(check-sat)
