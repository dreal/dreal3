(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.))) skoZ)) (not (<= skoZ (+ (+ (/ 3. 2.) (* skoX (- 1.))) (* skoY (- 1.)))))))
(set-info :status sat)
(check-sat)
