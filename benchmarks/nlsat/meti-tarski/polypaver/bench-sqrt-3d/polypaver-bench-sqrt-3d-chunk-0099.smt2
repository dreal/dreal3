(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (* skoZ (* skoY (* skoY (- 1.))))) 0.)) (and (not (<= skoZ 1.)) (or (not (<= skoX 1.)) (or (not (<= skoY 1.)) (not (<= skoZ 1.)))))))
(set-info :status unsat)
(check-sat)
