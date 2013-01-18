(set-logic QF_NRA)

(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoSP1 (+ (- 6.) (* skoSP1 12.))) (- 1.)) (and (not (<= (* skoSM1 (+ (- 12.) (* skoSM1 (+ 60. (* skoSM1 (- 120.)))))) (- 1.))) (and (= (+ (- 1.) (* skoSP1 skoSP1)) skoX) (and (= (+ 1. (* skoSM1 skoSM1)) skoX) (and (= (* skoS skoS) skoX) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX))))))))))))
(set-info :status unsat)
(check-sat)
