(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (not (<= (* skoZ (+ (+ (/ 9891. 100.) (* skoX (+ (- 63.) (* skoX (+ (/ 1099. 10.) (* skoX (+ (- 49.) (* skoX (+ (/ 471. 20.) (* skoX (/ (- 64.) 15.))))))))))) (* skoY (+ (+ (- 63.) (* skoX (+ (/ (- 9891.) 100.) (* skoX (+ (- 7.) (* skoX (+ (/ (- 1099.) 10.) (* skoX (+ 34. (* skoX (+ (/ (- 471.) 20.) (* skoX (/ 64. 15.))))))))))))) (* skoY (* skoX (+ 63. (* skoX (* skoX (+ 70. (* skoX (* skoX 15.)))))))))))) (+ (+ 63. (* skoX (+ (/ (- 9891.) 100.) (* skoX (+ 133. (* skoX (+ (/ (- 1099.) 10.) (* skoX (+ 64. (* skoX (+ (/ (- 471.) 20.) (* skoX (/ 64. 15.))))))))))))) (* skoY (+ (+ (/ (- 9891.) 100.) (* skoX (+ 63. (* skoX (+ (/ (- 1099.) 10.) (* skoX (+ 49. (* skoX (+ (/ (- 471.) 20.) (* skoX (/ 64. 15.))))))))))) (* skoY (+ 63. (* skoX (* skoX (+ 70. (* skoX (* skoX 15.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
