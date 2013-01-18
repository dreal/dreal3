(set-logic QF_NRA)

(declare-fun skoS2 () Real)
(declare-fun skoSP () Real)
(declare-fun skoSM () Real)
(declare-fun skoX () Real)
(assert (and (= skoX (+ 1. (* skoSM (* skoSM (- 1.))))) (and (= (+ (- 1.) (* skoSP skoSP)) skoX) (and (= (* skoS2 skoS2) 2.) (and (not (<= skoX 0.)) (and (not (<= skoSP 0.)) (and (not (<= skoSM 0.)) (and (not (<= skoS2 0.)) (not (<= 1. skoX))))))))))
(set-info :status sat)
(check-sat)
