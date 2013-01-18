(set-logic QF_NRA)

(declare-fun skoSP1 () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoSP1 (+ (+ (- 24.) (* skoSM1 (* skoSM1 (- 288.)))) (* skoSP1 (+ (* skoSM1 720.) (* skoSP1 (+ (- 240.) (* skoSM1 (* skoSM1 (- 2880.))))))))) (* skoSM1 (- 12.))) (and (not (<= (* skoSP1 (+ (+ 24. (* skoSM1 (+ (- 144.) (* skoSM1 288.)))) (* skoSP1 (+ (+ (- 120.) (* skoSM1 (+ 720. (* skoSM1 (- 1440.))))) (* skoSP1 (+ 240. (* skoSM1 (+ (- 1440.) (* skoSM1 2880.))))))))) (+ 2. (* skoSM1 (+ (- 12.) (* skoSM1 24.)))))) (and (= (+ (- 1.) (* skoSP1 skoSP1)) skoX) (and (= (+ 1. (* skoSM1 skoSM1)) skoX) (and (= (* skoS skoS) skoX) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX))))))))))))
(set-info :status sat)
(check-sat)
