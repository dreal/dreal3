(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (+ (+ (/ (- 673519.) 819200.) (* skoSXY (/ 36. 125.))) (* skoX (/ 18. 125.)))) (* skoSXY (/ (- 145681.) 409600.))) (and (<= skoX (* skoSXY (- 2.))) (and (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY))))))))))
(set-info :status unsat)
(check-sat)
