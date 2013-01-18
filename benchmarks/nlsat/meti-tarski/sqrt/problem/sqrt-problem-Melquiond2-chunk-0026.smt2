(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (+ (+ (/ (- 41.) 50.) (* skoSXY (/ 36. 125.))) (* skoX (/ 18. 125.)))) (* skoSXY (/ (- 9.) 25.))) (and (<= skoX (* skoSXY (- 2.))) (and (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY))))))))))
(set-info :status unsat)
(check-sat)
