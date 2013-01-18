(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoX () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(assert (and (= (* skoS skoS) skoX) (and (<= 0. skoSP1) (and (<= 0. skoSM1) (and (<= 0. skoS) (not (<= skoX (/ 7. 5.))))))))
(set-info :status sat)
(check-sat)
