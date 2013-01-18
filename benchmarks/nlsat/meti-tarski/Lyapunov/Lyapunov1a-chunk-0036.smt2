(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoZ (+ (/ (- 27.) 5.) (* skoZ (/ (- 81.) 100.)))) 12.) (and (not (<= skoZ 0.)) (and (<= skoZ (+ (* skoX (/ 127. 860.)) (* skoY (/ 493. 17200.)))) (and (or (not (<= (* skoZ (+ (+ (+ (/ 43. 250.) (* skoX (/ 229. 10000.))) (* skoY (/ 443. 100000.))) (* skoZ (/ (- 131.) 200.)))) (+ (* skoX (+ (/ 127. 5000.) (* skoX (/ 1. 2.)))) (* skoY (+ (/ 493. 100000.) (* skoY (/ 1. 2.))))))) (<= skoZ (+ (* skoX (/ 127. 860.)) (* skoY (/ 493. 17200.))))) (and (or (not (<= (+ (* skoX (/ 127. 860.)) (* skoY (/ 493. 17200.))) skoZ)) (not (<= skoZ (+ (* skoX (/ 127. 860.)) (* skoY (/ 493. 17200.)))))) (and (not (<= (* skoZ (+ (+ (* skoX (/ 213. 1000.)) (* skoY (/ 413. 10000.))) (* skoZ (/ (- 18.) 25.)))) (+ (+ (/ (- 1.) 10.) (* skoX (* skoX (/ 261. 100.)))) (* skoY (+ (* skoX (/ 21. 20.)) (* skoY (/ 141. 100.))))))) (or (not (= skoX 0.)) (or (not (= skoY 0.)) (not (= skoZ 0.)))))))))))
(set-info :status sat)
(check-sat)
