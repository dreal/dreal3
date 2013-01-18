(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ 3. (* skoX (* skoX (- 2.)))) (* skoY (+ (* skoX (+ (- 10.) (* skoX (* skoX 2.)))) (* skoY (+ (+ (- 2.) (* skoX (* skoX 7.))) (* skoY (* skoX 2.))))))) (* skoZ (+ (* skoX (- 1.)) (* skoY (+ (+ (- 1.) (* skoX (* skoX 2.))) (* skoY (+ (* skoX (+ 2. (* skoX (* skoX (- 1.))))) (* skoY (* skoX (* skoX (- 1.)))))))))))) (+ (* skoX (* skoX skoX)) (* skoY (* skoY (+ (* skoX (* skoX (* skoX 3.))) (* skoY (+ 1. (* skoX (* skoX 3.)))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
