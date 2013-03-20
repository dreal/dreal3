(set-logic QF_NRA_ODE)
(declare-fun x_t () Real)
(declare-fun x_0 () Real)
(declare-fun time_1 () Real)
(define-ode 1 (= d/dt[x] x))

(assert (<= 0.0 time_1))
(assert (<= time_1 3))

(assert (<= -10.0 x_0))
(assert (<= x_0 10))

(assert (<= 0.0 x_t))
(assert (<= x_t 100))

(assert (and 
		(= x_0 1.0)
		(>= x_t 6.4) 
		(<= x_t 7.5)
		(>= time_1 1.9)
		(<= time_1 2.1) 
	)
)
(check-sat)
(exit)
