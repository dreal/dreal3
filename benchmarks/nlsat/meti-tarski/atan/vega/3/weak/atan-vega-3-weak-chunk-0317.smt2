(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoY) (and (<= (* skoZ (+ (+ (* skoX (- 2.)) (* skoY (+ (+ (- 2.) (* skoX (* skoX 2.))) (* skoY (* skoX 2.))))) (* skoZ (+ (- 1.) (* skoY (+ (* skoX 2.) (* skoY (* skoX (* skoX (- 1.)))))))))) (+ (+ 3. (* skoX skoX)) (* skoY (+ (* skoX (- 4.)) (* skoY (+ 1. (* skoX (* skoX 3.)))))))) (and (not (<= 0. skoX)) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status sat)
(check-sat)
