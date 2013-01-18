(set-logic QF_NRA)

(declare-fun skoSP1 () Real)
(declare-fun skoS () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoSP1 0.)) (and (= (+ (- 1.) (* skoSP1 skoSP1)) skoX) (and (= (+ 1. (* skoSM1 skoSM1)) skoX) (and (= (* skoS skoS) skoX) (and (<= 0. skoSP1) (and (<= 0. skoSM1) (and (<= 0. skoS) (not (<= skoX (/ 7. 5.)))))))))))
(set-info :status sat)
(check-sat)
