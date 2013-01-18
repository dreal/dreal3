(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoW () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (+ (- 2.) (* skoW (* skoW (/ 1. 2.)))) (* skoX (+ skoW (* skoX (/ 1. 2.))))) (* skoY (+ (+ skoW skoX) (* skoY (/ 1. 2.))))) (* skoZ (+ (+ (+ (* skoW (/ 1. 2.)) (* skoX (/ 1. 2.))) (* skoY (/ 1. 2.))) (* skoZ (/ 1. 3.)))))) (+ (+ (* skoW (+ 2. (* skoW (* skoW (/ (- 1.) 6.))))) (* skoX (+ (+ 2. (* skoW (* skoW (/ (- 1.) 2.)))) (* skoX (+ (* skoW (/ (- 1.) 2.)) (* skoX (/ (- 1.) 3.))))))) (* skoY (+ (+ (+ 2. (* skoW (* skoW (/ (- 1.) 2.)))) (* skoX (+ (* skoW (- 1.)) (* skoX (/ (- 1.) 2.))))) (* skoY (+ (+ (* skoW (/ (- 1.) 2.)) (* skoX (/ (- 1.) 2.))) (* skoY (/ (- 1.) 3.))))))))) (and (not (<= 3. skoW)) (and (not (<= 3. skoX)) (and (not (<= 3. skoY)) (and (not (<= 3. skoZ)) (and (not (<= skoW (/ 1. 10.))) (and (not (<= skoX (/ 1. 10.))) (and (not (<= skoY (/ 1. 10.))) (not (<= skoZ (/ 1. 10.))))))))))))
(set-info :status sat)
(check-sat)
