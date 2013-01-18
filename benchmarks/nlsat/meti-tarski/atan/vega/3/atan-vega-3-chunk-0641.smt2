(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoY)) (and (not (<= (* skoZ (+ (+ (* skoX (- 126.)) (* skoY (+ (+ (- 126.) (* skoX (* skoX 126.))) (* skoY (+ (* skoX (- 14.)) (* skoY (+ (+ (- 140.) (* skoX (* skoX 140.))) (* skoY (+ (* skoX 110.) (* skoY (+ (+ (- 30.) (* skoX (* skoX 30.))) (* skoY (* skoX 30.))))))))))))) (* skoZ (+ (- 63.) (* skoY (+ (* skoX 126.) (* skoY (+ (+ (- 70.) (* skoX (* skoX (- 63.)))) (* skoY (+ (* skoX 140.) (* skoY (+ (+ (- 15.) (* skoX (* skoX (- 70.)))) (* skoY (+ (* skoX 30.) (* skoY (* skoX (* skoX (- 15.)))))))))))))))))) (+ (+ 189. (* skoX (* skoX 63.))) (* skoY (+ (* skoX (- 252.)) (* skoY (+ (+ 273. (* skoX (* skoX 259.))) (* skoY (+ (* skoX (- 280.)) (* skoY (+ (+ 115. (* skoX (* skoX 225.))) (* skoY (+ (* skoX (- 60.)) (* skoY (+ 15. (* skoX (* skoX 45.))))))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)

