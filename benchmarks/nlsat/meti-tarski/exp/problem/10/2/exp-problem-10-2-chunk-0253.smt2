(set-logic QF_NRA)

(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoSM1 (+ (- 12.) (* skoSM1 (+ 60. (* skoSM1 (- 120.)))))) (- 1.)) (and (not (<= (* skoSP1 (+ (+ 12. (* skoSM1 (+ (- 144.) (* skoSM1 (+ 720. (* skoSM1 (- 1440.))))))) (* skoSP1 (+ (- 24.) (* skoSM1 (+ 288. (* skoSM1 (+ (- 1440.) (* skoSM1 2880.))))))))) (+ 2. (* skoSM1 (+ (- 24.) (* skoSM1 (+ 120. (* skoSM1 (- 240.))))))))) (and (= (+ (- 1.) (* skoSP1 skoSP1)) skoX) (and (= (+ 1. (* skoSM1 skoSM1)) skoX) (and (= (* skoS skoS) skoX) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX))))))))))))
(set-info :status sat)
(check-sat)
