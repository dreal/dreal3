(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY 256.)))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY 160.))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY 32.)))) (* skoX (* skoSXY (* skoSXY skoSXY))))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (- 128.)))))))))) (and (not (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 59119.) 3200.) (* skoSXY (/ 2304. 125.))))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 427759.) 5120.) (* skoSXY (/ 4608. 125.)))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 1287919.) 25600.) (* skoSXY (/ 576. 25.))))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (+ (/ (- 5588719.) 819200.) (* skoSXY (/ 576. 125.)))))) (* skoX (* skoSXY (* skoSXY (* skoSXY (/ 18. 125.))))))))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (/ (- 145681.) 6400.)))))))))) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY)))))))))
(set-info :status sat)
(check-sat)
