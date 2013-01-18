(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= (* skoZ (+ (+ (/ 91. 50.) (* skoX (- 1.))) (* skoY (+ (+ (- 1.) (* skoX (+ (/ (- 91.) 50.) skoX))) (* skoY skoX))))) (+ (+ 1. (* skoX (+ (/ (- 91.) 50.) skoX))) (* skoY (+ (+ (/ (- 91.) 50.) skoX) skoY))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)
