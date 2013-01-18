(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= 0. skoSXY) (and (not (<= (/ 33. 32.) skoY)) (and (not (<= 2. skoX)) (and (not (<= skoSXY 0.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoY 1.)) (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY))))))))
(set-info :status sat)
(check-sat)
