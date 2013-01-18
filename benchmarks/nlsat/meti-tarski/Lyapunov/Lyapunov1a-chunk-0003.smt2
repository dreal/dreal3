(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (* skoX (/ 213. 1000.)) (* skoY (/ 413. 10000.))) (* skoZ (/ (- 18.) 25.)))) (+ (+ (/ (- 1.) 10.) (* skoX (* skoX (/ 261. 100.)))) (* skoY (+ (* skoX (/ 21. 20.)) (* skoY (/ 141. 100.)))))) (or (not (= skoX 0.)) (or (not (= skoY 0.)) (not (= skoZ 0.))))))
(set-info :status sat)
(check-sat)
