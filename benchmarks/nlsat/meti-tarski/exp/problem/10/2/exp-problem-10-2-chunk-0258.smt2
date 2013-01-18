(set-logic QF_NRA)

(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoSM1 (+ (- 12.) (* skoSM1 (+ 60. (* skoSM1 (- 120.)))))) (- 1.))) (and (not (<= (* skoSP1 (+ (+ (- 12.) (* skoSM1 (* skoSM1 (- 720.)))) (* skoSP1 (* skoSM1 (+ 288. (* skoSM1 (* skoSM1 2880.))))))) (* skoSM1 (+ (- 24.) (* skoSM1 (* skoSM1 (- 240.))))))) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX)))))))))
(set-info :status sat)
(check-sat)
