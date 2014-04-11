(set-logic QF_NRA_ODE)
(declare-fun a_t () Real)
(declare-fun a_0 () Real)

(declare-fun Fa_t () Real)
(declare-fun Fa_0 () Real)

(declare-fun t () Real)
(declare-fun t2 () Real)

(declare-fun time_0 () Real)

(define-ode flow_1((= d/dt[Fa] (/ 1.0 0.7854))(= d/dt[a] 1.0)))

(assert (<= 0.0 a_t))
(assert (<= a_t 0.7854))
(assert (<= 0.0 a_0))
(assert (<= a_0 0.7854))

(assert (<= 0.0 Fa_t))
(assert (<= Fa_t 2.0))
(assert (<= 0.0 Fa_0))
(assert (<= Fa_0 2.0))

(assert (<= 0.0 t))
(assert (>= 3.0 t))
(assert (<= 0.0 t2))
(assert (>= 3.0 t2))

(assert (and 
		(= Fa_0 0.0)		
		(>= Fa_t 0.0)

		(<= 30.0 (* 20.0 (* (cos a_0) t2)))
		(<= 31.0 (* 20.0 (* (cos a_t) t)))

		(<= 4.0 (- (* 20.0 (* (sin a_0) t2)) (/ (* 9.8 (^ t2 2)) 2)))
		(<= 5.0 (- (* 20.0 (* (sin a_t) t)) (/ (* 9.8 (^ t 2)) 2)))

		(= [a_t Fa_t] (integral 0 time_0 [a_0 Fa_0] flow_1))
	))
(check-sat)
(exit)
