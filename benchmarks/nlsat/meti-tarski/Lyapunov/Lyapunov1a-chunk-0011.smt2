(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (or (not (<= (+ (* skoX (/ 127. 860.)) (* skoY (/ 493. 17200.))) skoZ)) (not (<= skoZ (+ (* skoX (/ 127. 860.)) (* skoY (/ 493. 17200.)))))) (and (not (<= (* skoZ (+ (+ (* skoX (/ 213. 1000.)) (* skoY (/ 413. 10000.))) (* skoZ (/ (- 18.) 25.)))) (+ (+ (/ (- 1.) 10.) (* skoX (* skoX (/ 261. 100.)))) (* skoY (+ (* skoX (/ 21. 20.)) (* skoY (/ 141. 100.))))))) (or (not (= skoX 0.)) (or (not (= skoY 0.)) (not (= skoZ 0.)))))))
(set-info :status sat)
(check-sat)
