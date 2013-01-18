(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (+ 1. (* skoX (- 1.))) (* skoY (- 1.))) skoZ)) (and (not (<= skoZ (+ (+ (/ (- 32.) 5.) (* skoX (- 1.))) (* skoY (- 1.))))) (and (not (<= skoZ 0.)) (and (not (<= skoY 0.)) (not (<= skoX 0.)))))))
(set-info :status sat)
(check-sat)
