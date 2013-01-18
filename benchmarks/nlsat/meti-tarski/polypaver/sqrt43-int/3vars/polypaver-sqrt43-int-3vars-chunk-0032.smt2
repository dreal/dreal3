(set-logic QF_NRA)

(declare-fun skoE () Real)
(declare-fun skoX () Real)
(declare-fun skoR () Real)
(assert (and (<= skoR 0.) (and (not (<= (* skoX (+ (/ (- 1.) 2.) (* skoE (+ (/ (- 3.) 2.) (* skoE (+ (/ (- 3.) 2.) (* skoE (/ (- 1.) 2.)))))))) (* skoR (* skoR (+ (/ (- 1.) 2.) (* skoE (+ 1. (* skoE (/ 1. 2.))))))))) (and (<= (* skoX (+ (/ 1. 2.) (* skoE (+ (/ 3. 2.) (* skoE (+ (/ 3. 2.) (* skoE (/ 1. 2.)))))))) (* skoR (* skoR (+ (/ 1. 2.) (* skoE (+ (- 1.) (* skoE (/ (- 1.) 2.)))))))) (and (<= (* skoX (* skoX (/ (- 1.) 4.))) (+ 1. (* skoR (- 1.)))) (and (<= (* skoX (+ 1. (* skoX (/ (- 1.) 4.)))) skoR) (and (<= skoE (/ 1. 32.)) (and (<= (/ (- 1.) 32.) skoE) (and (<= skoX 2.) (and (<= skoR 3.) (and (<= (/ 1. 2.) skoX) (<= 0. skoR))))))))))))
(set-info :status unsat)
(check-sat)
