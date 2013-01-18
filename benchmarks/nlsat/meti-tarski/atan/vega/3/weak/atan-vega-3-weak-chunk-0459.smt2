(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (/ (- 5733.) 50.) (* skoY (+ (+ 63. (* skoX (/ 5733. 50.))) (* skoY (+ (+ (/ (- 637.) 5.) (* skoX (- 63.))) (* skoY (+ (+ 49. (* skoX (/ 637. 5.))) (* skoY (+ (+ (/ (- 273.) 10.) (* skoX (- 49.))) (* skoY (+ (+ (/ 64. 15.) (* skoX (/ 273. 10.))) (* skoY (* skoX (/ (- 64.) 15.))))))))))))))) (+ (+ (- 63.) (* skoX (/ 5733. 50.))) (* skoY (+ (/ 5733. 50.) (* skoY (+ (+ (- 133.) (* skoX (/ 637. 5.))) (* skoY (+ (+ (/ 637. 5.) (* skoX 21.)) (* skoY (+ (+ (- 64.) (* skoX (/ 273. 10.))) (* skoY (+ (+ (/ 273. 10.) (* skoX (/ 161. 15.))) (* skoY (/ (- 64.) 15.))))))))))))))) (and (not (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (* skoX (- 1.)) (* skoY (- 1.))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
