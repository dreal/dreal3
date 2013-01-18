(set-logic QF_NRA)

(declare-fun skoSP1 () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoSP1 (+ (+ (- 24.) (* skoSM1 (* skoSM1 (- 288.)))) (* skoSP1 (+ (* skoSM1 720.) (* skoSP1 (+ (- 240.) (* skoSM1 (* skoSM1 (- 2880.))))))))) (* skoSM1 (- 12.)))) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX))))))))
(set-info :status sat)
(check-sat)
