(set-logic QF_NRA)

(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoSP1 (+ (+ (- 24.) (* skoSM1 (+ 288. (* skoSM1 (+ (- 1440.) (* skoSM1 2880.)))))) (* skoSP1 (+ (+ 120. (* skoSM1 (+ (- 1440.) (* skoSM1 (+ 7200. (* skoSM1 (- 14400.))))))) (* skoSP1 (+ (- 240.) (* skoSM1 (+ 2880. (* skoSM1 (+ (- 14400.) (* skoSM1 28800.))))))))))) (+ (- 2.) (* skoSM1 (+ 24. (* skoSM1 (+ (- 120.) (* skoSM1 240.))))))) (and (not (<= (* skoSM1 (+ 12. (* skoSM1 (+ (- 60.) (* skoSM1 120.))))) 1.)) (and (not (<= (* skoSP1 (+ (* skoSM1 (+ (- 288.) (* skoSM1 (* skoSM1 (- 2880.))))) (* skoSP1 (+ (+ 120. (* skoSM1 (* skoSM1 7200.))) (* skoSP1 (* skoSM1 (+ (- 2880.) (* skoSM1 (* skoSM1 (- 28800.)))))))))) (+ (- 2.) (* skoSM1 (* skoSM1 (- 120.)))))) (and (= (+ (- 1.) (* skoSP1 skoSP1)) skoX) (and (= (+ 1. (* skoSM1 skoSM1)) skoX) (and (= (* skoS skoS) skoX) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX)))))))))))))
(set-info :status unsat)
(check-sat)
