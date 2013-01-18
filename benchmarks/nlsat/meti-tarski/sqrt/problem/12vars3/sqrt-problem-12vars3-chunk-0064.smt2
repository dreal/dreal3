(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSX () Real)
(declare-fun skoSMX () Real)
(assert (and (not (<= (* skoX (+ (+ (+ (- 24.) (* skoSMX (- 6.))) (* skoSX (- 6.))) (* skoX (+ (+ (* skoSMX 24.) (* skoSX (- 24.))) (* skoX (+ (+ 12. (* skoSMX 3.)) (* skoSX 3.))))))) (+ (* skoSMX 36.) (* skoSX (- 36.))))) (not (<= skoX 0.))))
(set-info :status sat)
(check-sat)
