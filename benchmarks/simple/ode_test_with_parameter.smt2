(set-logic QF_NRA_ODE)
(declare-fun x_t () Real)
(declare-fun x_0 () Real)
(declare-fun a_t () Real)
(declare-fun a_0 () Real)

(declare-fun time_1 () Real)
(define-ode 1 (= d/dt[x] (a * x)))
(define-ode 1 (= d/dt[a] 0))

(assert (<= 0.0 time_1))
(assert (<= time_1 3))

(assert (<= 0.0 a_0))
(assert (<= a_0 10))

(assert (<= 0.0 a_t))
(assert (<= a_t 10))

(assert (<= -10.0 x_0))
(assert (<= x_0 10))

(assert (<= 0.0 x_t))
(assert (<= x_t 100))

(assert (and
		(>= a_0 0.0)
		(>= a_t 0.0)

		(>= x_0 -10.0)
		(<= x_0 10.0)
		(>= x_t 27.4)
		(<= x_t 27.41)
		(>= time_1 1.9)
		(<= time_1 2.1)
	)
)
(check-sat)
(exit)
