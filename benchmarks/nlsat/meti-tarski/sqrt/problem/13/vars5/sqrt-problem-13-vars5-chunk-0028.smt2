(set-logic QF_NRA)

(declare-fun skoSS () Real)
(declare-fun skoSP () Real)
(declare-fun skoSM () Real)
(declare-fun skoS2 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoX (+ (+ (- 4.) (* skoSM (- 1.))) (* skoSP (- 1.)))) (+ (+ (* skoSM (+ 1. (* skoS2 2.))) (* skoSP (+ (- 1.) (* skoS2 (- 2.))))) (* skoSS (+ (* skoSM (+ (/ 1. 2.) skoS2)) (* skoSP (+ (/ (- 1.) 2.) (* skoS2 (- 1.))))))))) (and (not (<= skoSS (- 2.))) (and (not (<= skoX 0.)) (not (<= (/ 4. 5.) skoX))))))
(set-info :status sat)
(check-sat)

