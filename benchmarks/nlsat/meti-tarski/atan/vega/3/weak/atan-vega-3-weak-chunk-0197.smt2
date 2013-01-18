(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (- 3.) (* skoY (+ (* skoX 3.) (* skoY (+ (- 1.) (* skoY skoX))))))) (+ (* skoX 3.) (* skoY (+ 3. (* skoY (+ skoX skoY))))))) (and (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
