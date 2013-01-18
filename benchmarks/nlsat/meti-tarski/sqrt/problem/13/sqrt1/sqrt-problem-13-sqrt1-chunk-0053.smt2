(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSS () Real)
(declare-fun skoSM () Real)
(assert (and (not (<= (* skoX (+ (+ (+ (/ 1543. 500.) skoSM) (* skoSS (/ (- 957.) 1000.))) (* skoX (/ 1. 2.)))) (+ (+ (/ 957. 250.) (* skoSM (/ (- 957.) 250.))) (* skoSS (+ (/ 957. 500.) (* skoSM (/ (- 957.) 500.))))))) (and (not (<= 1. skoX)) (not (<= skoX 0.)))))
(set-info :status sat)
(check-sat)
