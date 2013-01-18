(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSX () Real)
(declare-fun skoSMX () Real)
(assert (and (not (<= (* skoX (+ (+ (+ (- 12.) (* skoSMX (- 3.))) (* skoSX (- 3.))) (* skoX (+ (* skoSMX 6.) (* skoSX (- 6.)))))) (+ (* skoSMX 18.) (* skoSX (- 18.))))) (not (<= skoX 0.))))
(set-info :status sat)
(check-sat)
