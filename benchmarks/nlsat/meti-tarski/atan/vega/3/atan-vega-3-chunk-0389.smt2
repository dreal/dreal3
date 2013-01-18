(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (+ 27. (* skoX (* skoX (- 9.)))) (* skoY (+ (* skoX (+ (- 90.) (* skoX (* skoX (- 6.))))) (* skoY (+ (+ (- 9.) (* skoX (* skoX (+ 54. (* skoX (* skoX 15.)))))) (* skoY (+ (* skoX (+ (- 6.) (* skoX (* skoX 6.)))) (* skoY (* skoX (* skoX (+ 15. (* skoX (* skoX 3.))))))))))))) (* skoZ (+ (* skoX (- 9.)) (* skoY (+ (+ (- 9.) (* skoX (* skoX 15.))) (* skoY (+ (* skoX (+ 15. (* skoX (* skoX (- 3.))))) (* skoY (+ (* skoX (* skoX (+ (- 3.) (* skoX (* skoX (- 3.)))))) (* skoY (* skoX (* skoX (* skoX (- 3.))))))))))))))) (* skoY (+ (* skoX (* skoX (* skoX (* skoX 12.)))) (* skoY (+ (* skoX (* skoX (* skoX 24.))) (* skoY (+ (* skoX (* skoX (+ 24. (* skoX (* skoX 12.))))) (* skoY (* skoX (+ 12. (* skoX (* skoX 12.)))))))))))) (and (not (<= 0. skoY)) (and (not (<= (* skoX skoX) (- 3.))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status unsat)
(check-sat)
