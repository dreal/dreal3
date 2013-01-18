(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY 256.)))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY 160.))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY 32.)))) (* skoX (* skoSXY (* skoSXY skoSXY))))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (- 128.))))))))) (and (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 448.) 25.) (* skoSXY (/ 2304. 125.))))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 416.) 5.) (* skoSXY (/ 4608. 125.)))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 1256.) 25.) (* skoSXY (/ 576. 25.))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 341.) 50.) (* skoSXY (/ 576. 125.)))))) (* skoX (* skoSXY (* skoSXY (* skoSXY (/ 18. 125.))))))))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (/ (- 576.) 25.))))))))) (and (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY))))))))))
(set-info :status unsat)
(check-sat)
