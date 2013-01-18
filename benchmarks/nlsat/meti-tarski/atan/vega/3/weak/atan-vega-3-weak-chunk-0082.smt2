(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (or (not (<= 0. skoX)) (or (not (<= (* skoZ (+ (+ (/ (- 91.) 50.) skoX) (* skoY (+ (+ 1. (* skoX (+ (/ 91. 50.) (* skoX (- 1.))))) (* skoY (* skoX (- 1.))))))) (+ (+ (- 1.) (* skoX (+ (/ 91. 50.) (* skoX (- 1.))))) (* skoY (+ (+ (/ 91. 50.) (* skoX (- 1.))) (* skoY (- 1.))))))) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.)))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
