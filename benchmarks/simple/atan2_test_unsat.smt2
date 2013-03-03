(set-logic QF_NRA)

(declare-fun y () Real)
(declare-fun x () Real)

(assert (<= y -0.1))
(assert (<= -0.3  y))

(assert (<= x 1.0))
(assert (<= -1.0 x))

(assert (> (arctan2 y x) 0.0))

(check-sat)
(exit)
