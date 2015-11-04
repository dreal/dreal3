(set-logic QF_NRA_ODE)
(declare-fun x () Real)
(declare-fun P () Real)

(declare-fun x_0 () Real)
(declare-fun x_t () Real)

(declare-fun P_0 () Real)
(declare-fun P_t () Real)

(declare-fun time_0 () Real)

(define-ode flow_1 (
                    (= d/dt[x] 1.0)
                    (= d/dt[P] (* (/ 1.0 (^ (* 2.0 3.14159265359) 0.5)) (exp (/ (- 0.0 (^ (- x 0.0) 2.0)) 2.0))))))

(assert (<= -100.0 x_0))
(assert (<= x_0 100.0))

(assert (<= -100.0 x_t))
(assert (<= x_t 100.0))

(assert (<= 0.0 P_0))
(assert (<= P_0 1.0))

(assert (<= 0.0 P_t))
(assert (<= P_t 1.0))

(assert (<= 0.0 time_0))
(assert (<= time_0 40.0))

(assert (and
                (= x_0 0.0)
                (= P_0 0.0)
                (= x_t 10.0)
                (>= P_t 0.0)
                (= [x_t P_t] (integral 0. time_0 [x_0 P_0] flow_1))
))

(check-sat)
(exit)
