(set-logic QF_NRA)

(declare-fun skoSM () Real)
(declare-fun skoS2 () Real)
(declare-fun skoSP () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoSP (+ (/ 13. 8.) (* skoS2 (/ 63. 20.)))) (+ (/ (- 1.) 5.) (* skoSM (+ (/ 61. 40.) (* skoS2 (/ 63. 20.)))))) (and (= skoX (+ 1. (* skoSM (* skoSM (- 1.))))) (and (= (+ (- 1.) (* skoSP skoSP)) skoX) (and (= (* skoS2 skoS2) 2.) (and (not (<= skoX 0.)) (and (not (<= skoSP 0.)) (and (not (<= skoSM 0.)) (and (not (<= skoS2 0.)) (not (<= 1. skoX)))))))))))
(set-info :status unsat)
(check-sat)
