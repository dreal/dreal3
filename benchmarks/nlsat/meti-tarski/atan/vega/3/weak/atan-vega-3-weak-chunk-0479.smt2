(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoX) (and (<= (* skoZ (+ (+ (/ (- 5733.) 50.) (* skoX 63.)) (* skoY (+ (+ 63. (* skoX (+ (/ 5733. 50.) (* skoX (- 63.))))) (* skoY (+ (+ (/ (- 637.) 5.) (* skoX 7.)) (* skoY (+ (+ 49. (* skoX (+ (/ 637. 5.) (* skoX (- 70.))))) (* skoY (+ (+ (/ (- 273.) 10.) (* skoX (- 34.))) (* skoY (+ (+ (/ 64. 15.) (* skoX (+ (/ 273. 10.) (* skoX (- 15.))))) (* skoY (* skoX (/ (- 64.) 15.))))))))))))))) (+ (+ (- 63.) (* skoX (+ (/ 5733. 50.) (* skoX (- 63.))))) (* skoY (+ (+ (/ 5733. 50.) (* skoX (- 63.))) (* skoY (+ (+ (- 133.) (* skoX (+ (/ 637. 5.) (* skoX (- 70.))))) (* skoY (+ (+ (/ 637. 5.) (* skoX (- 49.))) (* skoY (+ (+ (- 64.) (* skoX (+ (/ 273. 10.) (* skoX (- 15.))))) (* skoY (+ (+ (/ 273. 10.) (* skoX (/ (- 64.) 15.))) (* skoY (/ (- 64.) 15.)))))))))))))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))
(set-info :status sat)
(check-sat)
