(set-logic QF_NRA)
(declare-fun x () Real)
(assert (< 0.0 x))
(assert (< x 10.0))
(assert (= (^ x 0.000001) 7))
(check-sat)
(exit)
