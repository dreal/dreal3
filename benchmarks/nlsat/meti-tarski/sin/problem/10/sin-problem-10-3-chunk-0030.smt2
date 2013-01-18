(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoCP1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoCP1 (* skoCM1 2.)) 0.)) (not (<= skoX (/ 7. 5.)))))
(set-info :status sat)
(check-sat)
