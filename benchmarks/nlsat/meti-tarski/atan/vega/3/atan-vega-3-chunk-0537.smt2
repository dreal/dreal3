(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ 189. (* skoX (* skoX 63.))) (* skoY (+ (* skoX (+ (- 189.) (* skoX (* skoX (- 63.))))) (* skoY (+ (+ 210. (* skoX (* skoX 70.))) (* skoY (+ (* skoX (+ (- 210.) (* skoX (* skoX (- 70.))))) (* skoY (+ (+ 45. (* skoX (* skoX 15.))) (* skoY (* skoX (+ (- 45.) (* skoX (* skoX (- 15.)))))))))))))))) (+ (* skoX (* skoX (* skoX (- 63.)))) (* skoY (+ (* skoX (* skoX (- 189.))) (* skoY (+ (* skoX (+ (- 189.) (* skoX (* skoX (- 133.))))) (* skoY (+ (+ (- 63.) (* skoX (* skoX (- 231.)))) (* skoY (+ (* skoX (+ (- 147.) (* skoX (* skoX (- 64.))))) (* skoY (+ (+ (/ (- 161.) 5.) (* skoX (* skoX (/ (- 836.) 15.)))) (* skoY (* skoX (+ (/ (- 64.) 5.) (* skoX (* skoX (/ (- 64.) 15.))))))))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
