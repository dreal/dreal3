(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (- 24.)))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (- 10.))))) (* skoX (* skoSXY (* skoSXY (* skoSXY (- 1.))))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY 16.)))))))) (and (not (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 371507.) 102400.) (* skoSXY (/ 288. 125.)))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 669969.) 81920.) (* skoSXY (/ 432. 125.))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 2308369.) 819200.) (* skoSXY (/ 36. 25.)))))) (* skoX (* skoSXY (* skoSXY (+ (/ (- 1.) 8.) (* skoSXY (/ 18. 125.)))))))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (/ (- 149231.) 51200.))))))))) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY)))))))))
(set-info :status unsat)
(check-sat)
