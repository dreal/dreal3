(set-logic QF_NRA)

(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoSM1 () Real)
(assert (and (not (<= (* skoSP1 (+ (- 12.) (* skoSP1 (+ 60. (* skoSP1 (- 120.)))))) (- 1.))) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX))))))))
(set-info :status sat)
(check-sat)
