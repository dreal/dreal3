(set-logic QF_NRA)

(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoSP1 (* skoSM1 (- 2.))) 0.)) (not (<= skoX (/ 7. 5.)))))
(set-info :status sat)
(check-sat)
