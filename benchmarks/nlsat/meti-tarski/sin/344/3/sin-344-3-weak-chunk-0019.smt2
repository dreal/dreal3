(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (- 1.) (* skoX (* skoX (/ 1. 2.)))) (* skoY (+ skoX (* skoY (/ 1. 2.))))) (* skoZ (+ (+ (* skoX (/ 1. 2.)) (* skoY (/ 1. 2.))) (* skoZ (/ 1. 6.)))))) (+ (* skoX (+ 1. (* skoX (* skoX (/ (- 1.) 6.))))) (* skoY (+ (+ 1. (* skoX (* skoX (/ (- 1.) 2.)))) (* skoY (+ (* skoX (/ (- 1.) 2.)) (* skoY (/ (- 1.) 6.))))))))) (and (not (<= (/ 11. 10.) skoX)) (and (not (<= (/ 11. 10.) skoY)) (and (not (<= (/ 11. 10.) skoZ)) (and (not (<= skoX (/ 1. 10.))) (and (not (<= skoY (/ 1. 10.))) (not (<= skoZ (/ 1. 10.))))))))))
(set-info :status sat)
(check-sat)
