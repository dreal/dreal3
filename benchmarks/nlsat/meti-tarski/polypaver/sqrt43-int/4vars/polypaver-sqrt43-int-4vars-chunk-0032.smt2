(set-logic QF_NRA)

(declare-fun skoE () Real)
(declare-fun skoR () Real)
(declare-fun skoX () Real)
(declare-fun skoEA () Real)
(assert (not (<= (* skoX (+ (/ 1. 2.) (* skoE (+ (/ 3. 2.) (* skoE (+ (/ 3. 2.) (* skoE (/ 1. 2.)))))))) (* skoR (+ (* skoEA (+ (- 2.) (* skoE (+ (/ (- 3.) 2.) (* skoE (/ (- 1.) 2.)))))) (* skoR (+ (/ 1. 2.) (* skoE (+ (- 1.) (* skoE (/ (- 1.) 2.)))))))))))
(set-info :status sat)
(check-sat)
