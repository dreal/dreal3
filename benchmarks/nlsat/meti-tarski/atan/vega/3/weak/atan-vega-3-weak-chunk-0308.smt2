(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoX) (and (<= (* skoZ (+ (+ (* skoX 2.) (* skoY (+ (+ 2. (* skoX (* skoX (- 2.)))) (* skoY (* skoX (- 2.)))))) (* skoZ (+ 1. (* skoY (+ (* skoX (- 2.)) (* skoY (* skoX skoX)))))))) (+ (+ (- 3.) (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX 4.) (* skoY (+ (- 1.) (* skoX (* skoX (- 3.))))))))) (and (<= (* skoZ (+ (+ (+ (- 3.) (* skoX (+ (/ (- 1.) 2.) (* skoX 2.)))) (* skoY (+ (+ (/ (- 1.) 2.) (* skoX (+ 10. (* skoX (+ (/ 1. 2.) (* skoX (- 2.))))))) (* skoY (+ (+ 2. (* skoX (+ (/ 1. 2.) (* skoX (- 7.))))) (* skoY (* skoX (- 2.)))))))) (* skoZ (+ (+ (/ (- 1.) 4.) skoX) (* skoY (+ (+ 1. (* skoX (+ (/ 1. 2.) (* skoX (- 2.))))) (* skoY (+ (* skoX (+ (- 2.) (* skoX (+ (/ (- 1.) 4.) skoX)))) (* skoY (* skoX skoX)))))))))) (+ (+ (/ 3. 4.) (* skoX (* skoX (+ (/ 1. 4.) (* skoX (- 1.)))))) (* skoY (+ (* skoX (- 1.)) (* skoY (+ (+ (/ 1. 4.) (* skoX (* skoX (+ (/ 3. 4.) (* skoX (- 3.)))))) (* skoY (+ (- 1.) (* skoX (* skoX (- 3.))))))))))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status unsat)
(check-sat)
