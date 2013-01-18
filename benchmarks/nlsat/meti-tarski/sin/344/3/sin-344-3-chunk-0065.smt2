(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= skoX 0.) (and (not (<= (* skoZ (+ (+ (+ (- 2.) (* skoX (* skoX (/ 1. 2.)))) (* skoY (+ skoX (* skoY (/ 1. 2.))))) (* skoZ (+ (+ (* skoX (/ 1. 2.)) (* skoY (/ 1. 2.))) (* skoZ (+ (/ 1. 3.) (* skoZ (* skoZ (+ (/ (- 1.) 120.) (* skoZ (* skoZ (/ 1. 5040.)))))))))))) (+ (* skoX (+ 2. (* skoX (* skoX (/ (- 1.) 6.))))) (* skoY (+ (+ 2. (* skoX (* skoX (/ (- 1.) 2.)))) (* skoY (+ (* skoX (/ (- 1.) 2.)) (* skoY (/ (- 1.) 3.))))))))) (and (not (<= 3. skoX)) (and (not (<= 3. skoY)) (and (not (<= 3. skoZ)) (and (not (<= skoX (/ 1. 10.))) (and (not (<= skoY (/ 1. 10.))) (not (<= skoZ (/ 1. 10.)))))))))))
(set-info :status unsat)
(check-sat)
