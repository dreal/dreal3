(set-logic QF_NRA)

(declare-fun skoSP () Real)
(declare-fun skoSM () Real)
(declare-fun skoX () Real)
(declare-fun skoSS () Real)
(assert (and (= skoX (+ 1. (* skoSM (* skoSM (- 1.))))) (and (= (+ (- 1.) (* skoSP skoSP)) skoX) (and (<= 0. skoX) (and (<= 0. skoSS) (and (<= 0. skoSP) (and (<= 0. skoSM) (not (<= 1. skoX)))))))))
(set-info :status sat)
(check-sat)
