(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoSXY (- 1.)) skoX) (and (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 92.) 25.) (* skoSXY (/ 288. 125.)))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 41.) 5.) (* skoSXY (/ 432. 125.))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 141.) 50.) (* skoSXY (/ 36. 25.)))))) (* skoX (* skoSXY (* skoSXY (+ (/ (- 1.) 8.) (* skoSXY (/ 18. 125.)))))))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (/ (- 72.) 25.)))))))) (and (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY))))))))))
(set-info :status sat)
(check-sat)
