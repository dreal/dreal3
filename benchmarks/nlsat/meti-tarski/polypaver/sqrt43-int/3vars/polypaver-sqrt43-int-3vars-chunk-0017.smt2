(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoR () Real)
(declare-fun skoE () Real)
(assert (and (<= (* skoX (+ 1. (* skoX (/ (- 1.) 4.)))) skoR) (and (<= skoE (/ 1. 32.)) (and (<= (/ (- 1.) 32.) skoE) (and (<= skoX 2.) (and (<= skoR 3.) (and (<= (/ 1. 2.) skoX) (<= 0. skoR))))))))
(set-info :status sat)
(check-sat)
