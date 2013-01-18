(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSS () Real)
(declare-fun skoSP () Real)
(declare-fun skoSM () Real)
(assert (and (not (<= (* skoX (+ (+ (- 4.) (* skoSM (- 1.))) (* skoSP (- 1.)))) (+ (+ (* skoSM (/ 957. 250.)) (* skoSP (/ (- 957.) 250.))) (* skoSS (+ (* skoSM (/ 957. 500.)) (* skoSP (/ (- 957.) 500.))))))) (and (not (<= skoSS (- 2.))) (and (= (* skoX skoX) (+ 1. (* skoSS (* skoSS (- 1.))))) (and (= skoX (+ 1. (* skoSM (* skoSM (- 1.))))) (and (= (+ (- 1.) (* skoSP skoSP)) skoX) (and (<= 0. skoX) (and (<= 0. skoSS) (and (<= 0. skoSP) (and (<= 0. skoSM) (not (<= 1. skoX))))))))))))
(set-info :status unsat)
(check-sat)
