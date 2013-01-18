(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (+ (- 1.) (* skoSXY (/ 36. 125.)))) (* skoSXY (/ (- 9.) 25.)))) (and (not (<= (/ 33. 32.) skoY)) (and (not (<= 2. skoX)) (and (not (<= skoSXY 0.)) (and (not (<= skoX (/ 3. 2.))) (not (<= skoY 1.))))))))
(set-info :status sat)
(check-sat)
