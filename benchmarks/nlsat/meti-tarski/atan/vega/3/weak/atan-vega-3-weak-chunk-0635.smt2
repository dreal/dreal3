(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (- 231.) (* skoY (+ (* skoX 231.) (* skoY (+ (- 315.) (* skoY (+ (* skoX 315.) (* skoY (+ (- 105.) (* skoY (+ (* skoX 105.) (* skoY (+ (- 5.) (* skoY (* skoX 5.)))))))))))))))) (+ (+ (/ 231. 4.) (* skoX 231.)) (* skoY (+ (* skoX (/ (- 231.) 4.)) (* skoY (+ (+ (/ 315. 4.) (* skoX 546.)) (* skoY (+ (+ 77. (* skoX (/ (- 315.) 4.))) (* skoY (+ (+ (/ 105. 4.) (* skoX 343.)) (* skoY (+ (+ (/ 294. 5.) (* skoX (/ (- 105.) 4.))) (* skoY (+ (+ (/ 5. 4.) (* skoX (/ 256. 5.))) (* skoY (+ 5. (* skoX (/ (- 5.) 4.))))))))))))))))))) (and (not (<= 0. skoY)) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
