(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (<= skoX 1.) (and (<= skoZ 1.) (and (not (<= (* skoZ (* skoY 2.)) 0.)) (and (not (<= (* skoZ (* skoY (+ (* skoX (/ (- 3.) 2.)) (* skoY (* skoX (/ 1. 2.)))))) (+ (/ (- 1.) 4.) (* skoY (/ (- 1.) 4.))))) (and (<= 1. skoX) (and (<= 1. skoY) (and (<= 1. skoZ) (and (<= skoX 2.) (and (<= skoY 2.) (and (<= skoZ 2.) (and (or (not (<= skoX 1.)) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))))))))))))))
(set-info :status unsat)
(check-sat)
