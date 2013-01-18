(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoX (* skoX (+ 315. (* skoX (* skoX (+ 105. (* skoX (* skoX 5.)))))))) (- 231.))) (and (not (<= (* skoZ (+ (+ (- 231.) (* skoX (* skoX (+ (- 315.) (* skoX (* skoX (+ (- 105.) (* skoX (* skoX (- 5.)))))))))) (* skoY (* skoX (+ 231. (* skoX (* skoX (+ 315. (* skoX (* skoX (+ 105. (* skoX (* skoX 5.))))))))))))) (+ (+ (/ 231. 4.) (* skoX (* skoX (+ (/ 315. 4.) (* skoX (+ 77. (* skoX (+ (/ 105. 4.) (* skoX (+ (/ 294. 5.) (* skoX (+ (/ 5. 4.) (* skoX 5.))))))))))))) (* skoY (+ (* skoX (+ (/ (- 231.) 4.) (* skoX (+ 231. (* skoX (+ (/ (- 315.) 4.) (* skoX (+ 238. (* skoX (+ (/ (- 105.) 4.) (* skoX (+ (/ 231. 5.) (* skoX (/ (- 5.) 4.)))))))))))))) (* skoY (* skoX (+ 231. (* skoX (* skoX (+ 315. (* skoX (* skoX (+ 105. (* skoX (* skoX 5.)))))))))))))))) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
