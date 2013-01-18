(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoW () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= skoZ (+ (+ (* skoW (- 1.)) (* skoX (- 1.))) (* skoY (- 1.))))) (and (not (<= 3. skoW)) (and (not (<= 3. skoX)) (and (not (<= 3. skoY)) (and (not (<= 3. skoZ)) (and (not (<= skoW (/ 1. 10.))) (and (not (<= skoX (/ 1. 10.))) (and (not (<= skoY (/ 1. 10.))) (not (<= skoZ (/ 1. 10.))))))))))))
(set-info :status sat)
(check-sat)
