(set-logic QF_NRA)

(declare-fun skoSM () Real)
(declare-fun skoX () Real)
(declare-fun skoSS () Real)
(assert (and (not (= skoX (+ 1. (* skoSM (* skoSM (- 1.)))))) (and (<= 0. skoSS) (and (<= 0. skoSM) (and (not (<= skoX 0.)) (not (<= 1. skoX)))))))
(set-info :status sat)
(check-sat)
