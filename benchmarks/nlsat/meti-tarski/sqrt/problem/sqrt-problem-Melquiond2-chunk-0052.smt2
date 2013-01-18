(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= 0. skoSXY) (and (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY)))))))))
(set-info :status sat)
(check-sat)
