(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (* skoX (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (/ 1. 24.)))))) (* skoY (+ (* skoX (+ (- 1.) (* skoX (* skoX (/ 1. 6.))))) (* skoY (+ (+ (/ (- 1.) 2.) (* skoX (* skoX (/ 1. 4.)))) (* skoY (+ (* skoX (/ 1. 6.)) (* skoY (/ 1. 24.))))))))) (* skoZ (+ (+ (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (/ 1. 12.))))) (* skoY (+ (+ (/ (- 1.) 2.) (* skoX (* skoX (/ 1. 4.)))) (* skoY (+ (* skoX (/ 1. 4.)) (* skoY (/ 1. 12.))))))) (* skoZ (+ (+ (* skoX (* skoX (/ 1. 12.))) (* skoY (+ (* skoX (/ 1. 6.)) (* skoY (/ 1. 12.))))) (* skoZ (+ (+ (* skoX (/ 1. 24.)) (* skoY (/ 1. 24.))) (* skoZ (/ 1. 120.)))))))))) (+ (+ (/ 1. 10.) (* skoX (* skoX (* skoX (+ (/ 1. 6.) (* skoX (* skoX (/ (- 1.) 120.)))))))) (* skoY (+ (* skoX (* skoX (+ (/ 1. 2.) (* skoX (* skoX (/ (- 1.) 24.)))))) (* skoY (+ (* skoX (+ (/ 1. 2.) (* skoX (* skoX (/ (- 1.) 12.))))) (* skoY (+ (* skoX (* skoX (/ (- 1.) 12.))) (* skoY (+ (* skoX (/ (- 1.) 24.)) (* skoY (/ (- 1.) 120.))))))))))))) (and (not (<= (* skoZ (* skoZ (* skoZ (/ 1. 6.)))) (+ (+ (/ 1. 10.) (* skoX (* skoX (* skoX (/ (- 1.) 6.))))) (* skoY (* skoY (* skoY (/ (- 1.) 6.))))))) (and (not (<= skoZ (/ 1. 10.))) (and (not (<= skoY (/ 1. 10.))) (and (not (<= skoX (/ 1. 10.))) (and (not (<= (/ 11. 10.) skoZ)) (and (not (<= (/ 11. 10.) skoY)) (not (<= (/ 11. 10.) skoX))))))))))
(set-info :status unsat)
(check-sat)
