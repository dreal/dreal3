(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (= (* skoSXY skoSXY) 0.)) (and (not (= skoSXY 0.)) (and (not (<= (/ 33. 32.) skoY)) (and (not (<= 2. skoX)) (and (not (<= skoSXY 0.)) (and (not (<= skoX (/ 3. 2.))) (not (<= skoY 1.)))))))))
(set-info :status sat)
(check-sat)
