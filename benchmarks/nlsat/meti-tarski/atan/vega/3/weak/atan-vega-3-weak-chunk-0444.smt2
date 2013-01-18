(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (- 63.) (* skoY (+ (* skoX 63.) (* skoY (+ (- 70.) (* skoY (+ (* skoX 70.) (* skoY (+ (- 15.) (* skoY (* skoX 15.)))))))))))) (+ (+ (/ 63. 4.) (* skoX 63.)) (* skoY (+ (* skoX (/ (- 63.) 4.)) (* skoY (+ (+ (/ 35. 2.) (* skoX 133.)) (* skoY (+ (+ 21. (* skoX (/ (- 35.) 2.))) (* skoY (+ (+ (/ 15. 4.) (* skoX 64.)) (* skoY (+ (+ (/ 161. 15.) (* skoX (/ (- 15.) 4.))) (* skoY (* skoX (/ 64. 15.)))))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
