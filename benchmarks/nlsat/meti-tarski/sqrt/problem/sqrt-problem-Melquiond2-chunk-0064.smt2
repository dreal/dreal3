(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (+ (- 1.) (* skoSXY (/ 36. 125.)))) (* skoSXY (/ (- 9.) 25.))) (and (not (<= (/ 33. 32.) skoY)) (and (not (<= 2. skoX)) (and (not (<= skoSXY 0.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoY 1.)) (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY))))))))
(set-info :status sat)
(check-sat)
