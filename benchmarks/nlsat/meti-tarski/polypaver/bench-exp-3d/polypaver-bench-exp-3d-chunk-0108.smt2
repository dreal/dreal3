(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (<= (* skoZ (+ (+ (+ (- 60.) (* skoX (+ 36. (* skoX (+ (- 9.) skoX))))) (* skoY (+ (+ 36. (* skoX (+ (- 18.) (* skoX 3.)))) (* skoY (+ (+ (- 9.) (* skoX 3.)) skoY))))) (* skoZ (+ (+ (+ 48. (* skoX (+ (- 21.) (* skoX 3.)))) (* skoY (+ (+ (- 21.) (* skoX 6.)) (* skoY 3.)))) (* skoZ (+ (+ (+ (- 11.) (* skoX 3.)) (* skoY 3.)) skoZ)))))) (+ (+ 120. (* skoX (+ (- 60.) (* skoX (+ 12. (* skoX (- 1.))))))) (* skoY (+ (+ (- 60.) (* skoX (+ 24. (* skoX (- 3.))))) (* skoY (+ (+ 12. (* skoX (- 3.))) (* skoY (- 1.))))))))))
(set-info :status sat)
(check-sat)
