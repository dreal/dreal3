(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSS () Real)
(declare-fun skoSM () Real)
(assert (and (<= skoX (+ (/ 957. 250.) (* skoSS (/ 957. 500.)))) (and (not (<= (+ (/ 957. 250.) (* skoSS (/ 957. 500.))) skoX)) (and (not (<= 1. skoX)) (and (not (<= skoX 0.)) (and (<= 0. skoSM) (and (<= 0. skoSS) (and (= skoX (+ 1. (* skoSM (* skoSM (- 1.))))) (= (* skoX skoX) (+ 1. (* skoSS (* skoSS (- 1.)))))))))))))
(set-info :status sat)
(check-sat)
