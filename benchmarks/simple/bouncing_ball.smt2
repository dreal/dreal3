(set-logic QF_NRA_ODE)
(declare-fun time () Real)
(declare-fun x_0 () Real)
(declare-fun x_t () Real)
(define-ode (= d/dt[x] 1))


(assert (<= time 3.5))
(assert (<= 3.0 time))

(assert (<= x_0 1000))
(assert (<= -100 x_0))
(assert (<= -1000 x_t))
(assert (<= x_t 9999))

(assert
    (and (> x_0 0) (< x_0 0.5) (> x_t 2))
)
(check-sat)
(exit)
