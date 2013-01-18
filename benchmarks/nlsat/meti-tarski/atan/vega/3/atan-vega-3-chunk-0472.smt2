(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= (* skoZ (+ (+ (* skoX 6.) (* skoY (+ (+ 6. (* skoX (* skoX (- 6.)))) (* skoY (* skoX (- 6.)))))) (* skoZ (+ 3. (* skoY (+ (* skoX (- 6.)) (* skoY (* skoX (* skoX 3.))))))))) (+ (+ (- 1.) (* skoX (* skoX (- 3.)))) (* skoY (+ (* skoX (- 4.)) (* skoY (+ (- 3.) (* skoX (* skoX (- 1.)))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
