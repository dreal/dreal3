(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (not (<= (* skoZ (+ (+ (+ (- 60.) (* skoX (+ 24. (* skoX (- 3.))))) (* skoY (+ (+ 24. (* skoX (- 6.))) (* skoY (- 3.))))) (* skoZ (+ (+ (+ 12. (* skoX (- 3.))) (* skoY (- 3.))) (* skoZ (- 1.)))))) (+ (+ (- 120.) (* skoX (+ 60. (* skoX (+ (- 12.) skoX))))) (* skoY (+ (+ 60. (* skoX (+ (- 24.) (* skoX 3.)))) (* skoY (+ (+ (- 12.) (* skoX 3.)) skoY))))))))
(set-info :status sat)
(check-sat)
