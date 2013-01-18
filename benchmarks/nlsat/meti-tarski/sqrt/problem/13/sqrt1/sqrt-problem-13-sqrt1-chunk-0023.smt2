(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSM () Real)
(declare-fun skoSS () Real)
(assert (and (not (<= (+ (- 10.) (* skoSM (- 2.))) skoX)) (and (= (* skoX skoX) (+ 1. (* skoSS (* skoSS (- 1.))))) (and (= skoX (+ 1. (* skoSM (* skoSM (- 1.))))) (and (<= 0. skoSS) (and (<= 0. skoSM) (and (not (<= skoX 0.)) (not (<= 1. skoX)))))))))
(set-info :status unsat)
(check-sat)
