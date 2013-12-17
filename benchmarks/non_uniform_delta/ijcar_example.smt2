(set-logic QF_NRA)

(declare-fun z () Real)
(declare-fun y () Real)
(declare-fun x () Real)

(assert (<= z 1.0))
(assert (<= -1.0 z))

(assert (<= y 1.0))
(assert (<= -1.0 y))

(assert (<= x 1.0))
(assert (<= -1.0 x))

(assert (=> (< (pow 2.71 z) x [0.5]) 
	    (< y (sin x) [0.05])))

(check-sat)
(exit)
