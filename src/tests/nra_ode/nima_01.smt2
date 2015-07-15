(set-logic QF_NRA_ODE)
(declare-fun x () Real)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(define-ode flow_0 ((= d/dt[x] x)))
(declare-fun t_0 () Real)
(assert (and (<= 0 t_0) (<= t_0 1)))
(assert (and (= [x_1] (integral 0. t_0 [x_2] flow_0)) (forall_t 1.0 [0.0 t_0] (and (<= 0 x_2) (<= x_2 0)))))
(check-sat)
(exit)


