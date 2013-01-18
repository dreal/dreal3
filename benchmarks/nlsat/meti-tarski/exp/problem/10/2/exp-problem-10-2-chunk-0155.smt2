(set-logic QF_NRA)

(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoSP1 (+ (+ (- 12.) (* skoSM1 (+ 72. (* skoSM1 (- 144.))))) (* skoSP1 (+ 24. (* skoSM1 (+ (- 144.) (* skoSM1 288.))))))) (+ (- 2.) (* skoSM1 (+ 12. (* skoSM1 (- 24.))))))) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX))))))))
(set-info :status sat)
(check-sat)
