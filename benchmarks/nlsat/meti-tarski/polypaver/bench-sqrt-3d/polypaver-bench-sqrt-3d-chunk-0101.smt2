(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= skoY 1.) (and (<= skoZ 1.) (and (not (<= (* skoZ (* skoZ (* skoY skoY))) 0.)) (and (not (<= (* skoZ (+ (* skoY (* skoX (/ 1. 4.))) (* skoZ (* skoY (* skoY (* skoX (+ (- 1.) (* skoX (/ 1. 4.))))))))) (/ (- 1.) 16.))) (and (or (not (<= skoX 1.)) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))) (and (<= skoZ 2.) (and (<= skoY 2.) (and (<= skoX 2.) (and (<= 1. skoZ) (and (<= 1. skoY) (<= 1. skoX))))))))))))
(set-info :status unsat)
(check-sat)
