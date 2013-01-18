(set-logic QF_NRA)

(declare-fun skoSP () Real)
(declare-fun skoX () Real)
(declare-fun skoS2 () Real)
(declare-fun skoSM () Real)
(assert (and (not (= (+ (- 1.) (* skoSP skoSP)) skoX)) (and (not (<= skoX 0.)) (and (not (<= skoSP 0.)) (and (not (<= skoSM 0.)) (and (not (<= skoS2 0.)) (not (<= 1. skoX))))))))
(set-info :status sat)
(check-sat)
