(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoY) (and (<= (* skoZ (+ (+ (* skoX 18.) (* skoY (+ (+ 18. (* skoX (* skoX (- 18.)))) (* skoY (+ (* skoX (- 12.)) (* skoY (+ (+ 6. (* skoX (* skoX (- 6.)))) (* skoY (* skoX (- 6.)))))))))) (* skoZ (+ 9. (* skoY (+ (* skoX (- 18.)) (* skoY (+ (+ 3. (* skoX (* skoX 9.))) (* skoY (+ (* skoX (- 6.)) (* skoY (* skoX (* skoX 3.))))))))))))) (+ (+ (- 3.) (* skoX (* skoX (- 9.)))) (* skoY (+ (* skoX (- 12.)) (* skoY (+ (+ (- 10.) (* skoX (* skoX (- 6.)))) (* skoY (+ (* skoX (- 4.)) (* skoY (+ (- 3.) (* skoX (* skoX (- 1.))))))))))))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))
(set-info :status unsat)
(check-sat)
