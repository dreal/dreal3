(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoX skoX) (- 3.))) (and (not (<= (* skoZ (+ (+ (- 693.) (* skoX (* skoX (- 231.)))) (* skoY (+ (* skoX (+ 693. (* skoX (* skoX 231.)))) (* skoY (+ (+ (- 945.) (* skoX (* skoX (- 315.)))) (* skoY (+ (* skoX (+ 945. (* skoX (* skoX 315.)))) (* skoY (+ (+ (- 315.) (* skoX (* skoX (- 105.)))) (* skoY (+ (* skoX (+ 315. (* skoX (* skoX 105.)))) (* skoY (+ (+ (- 15.) (* skoX (* skoX (- 5.)))) (* skoY (* skoX (+ 15. (* skoX (* skoX 5.))))))))))))))))))) (+ (+ (/ 693. 4.) (* skoX (* skoX (+ (/ 231. 4.) (* skoX 231.))))) (* skoY (+ (* skoX (+ (/ (- 693.) 4.) (* skoX (+ 693. (* skoX (/ (- 231.) 4.)))))) (* skoY (+ (+ (/ 945. 4.) (* skoX (+ 693. (* skoX (+ (/ 315. 4.) (* skoX 546.)))))) (* skoY (+ (+ 231. (* skoX (+ (/ (- 945.) 4.) (* skoX (+ 1022. (* skoX (/ (- 315.) 4.))))))) (* skoY (+ (+ (/ 315. 4.) (* skoX (+ 714. (* skoX (+ (/ 105. 4.) (* skoX 343.)))))) (* skoY (+ (+ (/ 882. 5.) (* skoX (+ (/ (- 315.) 4.) (* skoX (+ (/ 1869. 5.) (* skoX (/ (- 105.) 4.))))))) (* skoY (+ (+ (/ 15. 4.) (* skoX (+ (/ 693. 5.) (* skoX (+ (/ 5. 4.) (* skoX (/ 256. 5.))))))) (* skoY (+ 15. (* skoX (+ (/ (- 15.) 4.) (* skoX (+ 20. (* skoX (/ (- 5.) 4.))))))))))))))))))))))) (and (not (<= 0. skoY)) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))
(set-info :status sat)
(check-sat)
