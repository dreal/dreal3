(set-logic QF_NRA_ODE)
(declare-fun tau () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(define-ode flow_1 ((= d/dt[x1] (* 0.015 (- 100 (+ (* (- 1 0.01) x1) (* 0.01 x2)))))
                    (= d/dt[x2] (* 0.045 (- 200 (+ (* (- 1 0.01) x2) (* 0.01 x1)))))
		    (= d/dt[tau] 1)))
(define-ode flow_2 ((= d/dt[x1] (* 0.015 (- 100 (+ (* (- 1 0.01) x1) (* 0.01 x2))))) 
                    (= d/dt[x2] (* -0.045 (+ (* (- 1 0.01) x2) (* 0.01 x1))))
		    (= d/dt[tau] 1)))
(define-ode flow_3 ((= d/dt[x1] (* -0.015 (+ (* (- 1 0.01) x1) (* 0.01 x2))))
                    (= d/dt[x2] (* 0.045 (- 200 (+ (* (- 1 0.01) x2) (* 0.01 x1)))))
		    (= d/dt[tau] 1)))
(define-ode flow_4 ((= d/dt[x1] (* -0.015 (+ (* (- 1 0.01) x1) (* 0.01 x2))))
                    (= d/dt[x2] (* -0.045 (+ (* (- 1 0.01) x2) (* 0.01 x1))))
		    (= d/dt[tau] 1)))
(declare-fun time_0 () Real)  
(declare-fun tau_0_0 () Real) 
(declare-fun tau_0_t () Real) 
(declare-fun mode_1_0 () Int) 
(declare-fun x1_0_0 () Real)  
(declare-fun x1_0_t () Real)  
(declare-fun mode_2_0 () Int)
(declare-fun x2_0_0 () Real)  
(declare-fun x2_0_t () Real)
(declare-fun time_1 () Real)  
(declare-fun tau_1_0 () Real) 
(declare-fun tau_1_t () Real) 
(declare-fun mode_1_1 () Int) 
(declare-fun x1_1_0 () Real)  
(declare-fun x1_1_t () Real)  
(declare-fun mode_2_1 () Int)
(declare-fun x2_1_0 () Real)  
(declare-fun x2_1_t () Real)
(declare-fun time_2 () Real)  
(declare-fun tau_2_0 () Real) 
(declare-fun tau_2_t () Real) 
(declare-fun mode_1_2 () Int) 
(declare-fun x1_2_0 () Real)  
(declare-fun x1_2_t () Real)  
(declare-fun mode_2_2 () Int)
(declare-fun x2_2_0 () Real)  
(declare-fun x2_2_t () Real)
(declare-fun time_3 () Real)  
(declare-fun tau_3_0 () Real) 
(declare-fun tau_3_t () Real) 
(declare-fun mode_1_3 () Int) 
(declare-fun x1_3_0 () Real)  
(declare-fun x1_3_t () Real)  
(declare-fun mode_2_3 () Int)
(declare-fun x2_3_0 () Real)  
(declare-fun x2_3_t () Real)
(declare-fun time_4 () Real)  
(declare-fun tau_4_0 () Real) 
(declare-fun tau_4_t () Real) 
(declare-fun mode_1_4 () Int) 
(declare-fun x1_4_0 () Real)  
(declare-fun x1_4_t () Real)  
(declare-fun mode_2_4 () Int)
(declare-fun x2_4_0 () Real)  
(declare-fun x2_4_t () Real)
(declare-fun time_5 () Real)  
(declare-fun tau_5_0 () Real) 
(declare-fun tau_5_t () Real) 
(declare-fun mode_1_5 () Int) 
(declare-fun x1_5_0 () Real)  
(declare-fun x1_5_t () Real)  
(declare-fun mode_2_5 () Int)
(declare-fun x2_5_0 () Real)  
(declare-fun x2_5_t () Real)
(assert (<= 0 time_0))  (assert (<= time_0 1))
(assert (<= 0 tau_0_0)) (assert (<= tau_0_0 1))
(assert (<= 0 tau_0_t)) (assert (<= tau_0_t 1))
(assert (<= -20 x1_0_0)) (assert (<= x1_0_0 100))
(assert (<= -20 x1_0_t)) (assert (<= x1_0_t 100))
(assert (<= -20 x2_0_0)) (assert (<= x2_0_0 100))
(assert (<= -20 x2_0_t)) (assert (<= x2_0_t 100))
(assert (<= 0 time_1))  (assert (<= time_1 1))
(assert (<= 0 tau_1_0)) (assert (<= tau_1_0 1))
(assert (<= 0 tau_1_t)) (assert (<= tau_1_t 1))
(assert (<= -20 x1_1_0)) (assert (<= x1_1_0 100))
(assert (<= -20 x1_1_t)) (assert (<= x1_1_t 100))
(assert (<= -20 x2_1_0)) (assert (<= x2_1_0 100))
(assert (<= -20 x2_1_t)) (assert (<= x2_1_t 100))
(assert (<= 0 time_2))  (assert (<= time_2 1))
(assert (<= 0 tau_2_0)) (assert (<= tau_2_0 1))
(assert (<= 0 tau_2_t)) (assert (<= tau_2_t 1))
(assert (<= -20 x1_2_0)) (assert (<= x1_2_0 100))
(assert (<= -20 x1_2_t)) (assert (<= x1_2_t 100))
(assert (<= -20 x2_2_0)) (assert (<= x2_2_0 100))
(assert (<= -20 x2_2_t)) (assert (<= x2_2_t 100))
(assert (<= 0 time_3))  (assert (<= time_3 1))
(assert (<= 0 tau_3_0)) (assert (<= tau_3_0 1))
(assert (<= 0 tau_3_t)) (assert (<= tau_3_t 1))
(assert (<= -20 x1_3_0)) (assert (<= x1_3_0 100))
(assert (<= -20 x1_3_t)) (assert (<= x1_3_t 100))
(assert (<= -20 x2_3_0)) (assert (<= x2_3_0 100))
(assert (<= -20 x2_3_t)) (assert (<= x2_3_t 100))
(assert (<= 0 time_4))  (assert (<= time_4 1))
(assert (<= 0 tau_4_0)) (assert (<= tau_4_0 1))
(assert (<= 0 tau_4_t)) (assert (<= tau_4_t 1))
(assert (<= -20 x1_4_0)) (assert (<= x1_4_0 100))
(assert (<= -20 x1_4_t)) (assert (<= x1_4_t 100))
(assert (<= -20 x2_4_0)) (assert (<= x2_4_0 100))
(assert (<= -20 x2_4_t)) (assert (<= x2_4_t 100))
(assert (<= 0 time_5))  (assert (<= time_5 1))
(assert (<= 0 tau_5_0)) (assert (<= tau_5_0 1))
(assert (<= 0 tau_5_t)) (assert (<= tau_5_t 1))
(assert (<= -20 x1_5_0)) (assert (<= x1_5_0 100))
(assert (<= -20 x1_5_t)) (assert (<= x1_5_t 100))
(assert (<= -20 x2_5_0)) (assert (<= x2_5_0 100))
(assert (<= -20 x2_5_t)) (assert (<= x2_5_t 100))
(assert (= tau_0_0 0))
(assert (= mode_1_0 2))
(assert (and (>= x1_0_0 (- 20 1)) (<= x1_0_0 (+ 20 1))))
(assert (= mode_2_0 2))
(assert (and (>= x2_0_0 (- 20 1)) (<= x2_0_0 (+ 20 1))))
(assert (and (>= tau_0_0 0) (<= tau_0_0 1)
             (>= tau_0_t 0) (<= tau_0_t 1)
             (forall_t 1 [0 time_0] (>= tau_0_t 0))
             (forall_t 2 [0 time_0] (<= tau_0_t 1))))
(assert (and (not (and (= mode_1_0 1) (= mode_1_0 2)))
             (not (and (= mode_2_0 1) (= mode_2_0 2)))))            
(assert (or (and (= mode_1_0 2) (= mode_2_0 2)
                 (= [x1_0_t x2_0_t tau_0_t] 
                    (integral 0. time_0 [x1_0_0 x2_0_0 tau_0_0] flow_1)))
            (and (= mode_1_0 2) (= mode_2_0 1)
                 (= [x1_0_t x2_0_t tau_0_t] 
                    (integral 0. time_0 [x1_0_0 x2_0_0 tau_0_0] flow_2)))
            (and (= mode_1_0 1) (= mode_2_0 2)
                 (= [x1_0_t x2_0_t tau_0_t] 
                    (integral 0. time_0 [x1_0_0 x2_0_0 tau_0_0] flow_3)))
            (and (= mode_1_0 1) (= mode_2_0 1)
                 (= [x1_0_t x2_0_t tau_0_t] 
                    (integral 0. time_0 [x1_0_0 x2_0_0 tau_0_0] flow_4)))))
(assert (and (= tau_0_t 1) (= tau_1_0 0)))
(assert (and (= x1_1_0 x1_0_t)))
(assert (or (and (<= x1_0_t 20) (= mode_1_1 2))
            (and (> x1_0_t 20) (= mode_1_1 1))))
(assert (and (= x2_1_0 x2_0_t)))
(assert (or (and (<= x2_0_t 20) (= mode_2_1 2))
            (and (> x2_0_t 20) (= mode_2_1 1))))
(assert (and (>= tau_1_0 0) (<= tau_1_0 1)
             (>= tau_1_t 0) (<= tau_1_t 1)
             (forall_t 1 [0 time_1] (>= tau_1_t 0))
             (forall_t 2 [0 time_1] (<= tau_1_t 1))))
(assert (and (not (and (= mode_1_1 1) (= mode_1_1 2)))
             (not (and (= mode_2_1 1) (= mode_2_1 2)))))            
(assert (or (and (= mode_1_1 2) (= mode_2_1 2)
                 (= [x1_1_t x2_1_t tau_1_t] 
                    (integral 0. time_1 [x1_1_0 x2_1_0 tau_1_0] flow_1)))
            (and (= mode_1_1 2) (= mode_2_1 1)
                 (= [x1_1_t x2_1_t tau_1_t] 
                    (integral 0. time_1 [x1_1_0 x2_1_0 tau_1_0] flow_2)))
            (and (= mode_1_1 1) (= mode_2_1 2)
                 (= [x1_1_t x2_1_t tau_1_t] 
                    (integral 0. time_1 [x1_1_0 x2_1_0 tau_1_0] flow_3)))
            (and (= mode_1_1 1) (= mode_2_1 1)
                 (= [x1_1_t x2_1_t tau_1_t] 
                    (integral 0. time_1 [x1_1_0 x2_1_0 tau_1_0] flow_4)))))
(assert (and (= tau_1_t 1) (= tau_2_0 0)))
(assert (and (= x1_2_0 x1_1_t)))
(assert (or (and (<= x1_1_t 20) (= mode_1_2 2))
            (and (> x1_1_t 20) (= mode_1_2 1))))
(assert (and (= x2_2_0 x2_1_t)))
(assert (or (and (<= x2_1_t 20) (= mode_2_2 2))
            (and (> x2_1_t 20) (= mode_2_2 1))))
(assert (and (>= tau_2_0 0) (<= tau_2_0 1)
             (>= tau_2_t 0) (<= tau_2_t 1)
             (forall_t 1 [0 time_2] (>= tau_2_t 0))
             (forall_t 2 [0 time_2] (<= tau_2_t 1))))
(assert (and (not (and (= mode_1_2 1) (= mode_1_2 2)))
             (not (and (= mode_2_2 1) (= mode_2_2 2)))))            
(assert (or (and (= mode_1_2 2) (= mode_2_2 2)
                 (= [x1_2_t x2_2_t tau_2_t] 
                    (integral 0. time_2 [x1_2_0 x2_2_0 tau_2_0] flow_1)))
            (and (= mode_1_2 2) (= mode_2_2 1)
                 (= [x1_2_t x2_2_t tau_2_t] 
                    (integral 0. time_2 [x1_2_0 x2_2_0 tau_2_0] flow_2)))
            (and (= mode_1_2 1) (= mode_2_2 2)
                 (= [x1_2_t x2_2_t tau_2_t] 
                    (integral 0. time_2 [x1_2_0 x2_2_0 tau_2_0] flow_3)))
            (and (= mode_1_2 1) (= mode_2_2 1)
                 (= [x1_2_t x2_2_t tau_2_t] 
                    (integral 0. time_2 [x1_2_0 x2_2_0 tau_2_0] flow_4)))))
(assert (and (= tau_2_t 1) (= tau_3_0 0)))
(assert (and (= x1_3_0 x1_2_t)))
(assert (or (and (<= x1_2_t 20) (= mode_1_3 2))
            (and (> x1_2_t 20) (= mode_1_3 1))))
(assert (and (= x2_3_0 x2_2_t)))
(assert (or (and (<= x2_2_t 20) (= mode_2_3 2))
            (and (> x2_2_t 20) (= mode_2_3 1))))
(assert (and (>= tau_3_0 0) (<= tau_3_0 1)
             (>= tau_3_t 0) (<= tau_3_t 1)
             (forall_t 1 [0 time_3] (>= tau_3_t 0))
             (forall_t 2 [0 time_3] (<= tau_3_t 1))))
(assert (and (not (and (= mode_1_3 1) (= mode_1_3 2)))
             (not (and (= mode_2_3 1) (= mode_2_3 2)))))            
(assert (or (and (= mode_1_3 2) (= mode_2_3 2)
                 (= [x1_3_t x2_3_t tau_3_t] 
                    (integral 0. time_3 [x1_3_0 x2_3_0 tau_3_0] flow_1)))
            (and (= mode_1_3 2) (= mode_2_3 1)
                 (= [x1_3_t x2_3_t tau_3_t] 
                    (integral 0. time_3 [x1_3_0 x2_3_0 tau_3_0] flow_2)))
            (and (= mode_1_3 1) (= mode_2_3 2)
                 (= [x1_3_t x2_3_t tau_3_t] 
                    (integral 0. time_3 [x1_3_0 x2_3_0 tau_3_0] flow_3)))
            (and (= mode_1_3 1) (= mode_2_3 1)
                 (= [x1_3_t x2_3_t tau_3_t] 
                    (integral 0. time_3 [x1_3_0 x2_3_0 tau_3_0] flow_4)))))
(assert (and (= tau_3_t 1) (= tau_4_0 0)))
(assert (and (= x1_4_0 x1_3_t)))
(assert (or (and (<= x1_3_t 20) (= mode_1_4 2))
            (and (> x1_3_t 20) (= mode_1_4 1))))
(assert (and (= x2_4_0 x2_3_t)))
(assert (or (and (<= x2_3_t 20) (= mode_2_4 2))
            (and (> x2_3_t 20) (= mode_2_4 1))))
(assert (and (>= tau_4_0 0) (<= tau_4_0 1)
             (>= tau_4_t 0) (<= tau_4_t 1)
             (forall_t 1 [0 time_4] (>= tau_4_t 0))
             (forall_t 2 [0 time_4] (<= tau_4_t 1))))
(assert (and (not (and (= mode_1_4 1) (= mode_1_4 2)))
             (not (and (= mode_2_4 1) (= mode_2_4 2)))))            
(assert (or (and (= mode_1_4 2) (= mode_2_4 2)
                 (= [x1_4_t x2_4_t tau_4_t] 
                    (integral 0. time_4 [x1_4_0 x2_4_0 tau_4_0] flow_1)))
            (and (= mode_1_4 2) (= mode_2_4 1)
                 (= [x1_4_t x2_4_t tau_4_t] 
                    (integral 0. time_4 [x1_4_0 x2_4_0 tau_4_0] flow_2)))
            (and (= mode_1_4 1) (= mode_2_4 2)
                 (= [x1_4_t x2_4_t tau_4_t] 
                    (integral 0. time_4 [x1_4_0 x2_4_0 tau_4_0] flow_3)))
            (and (= mode_1_4 1) (= mode_2_4 1)
                 (= [x1_4_t x2_4_t tau_4_t] 
                    (integral 0. time_4 [x1_4_0 x2_4_0 tau_4_0] flow_4)))))
(assert (and (= tau_4_t 1) (= tau_5_0 0)))
(assert (and (= x1_5_0 x1_4_t)))
(assert (or (and (<= x1_4_t 20) (= mode_1_5 2))
            (and (> x1_4_t 20) (= mode_1_5 1))))
(assert (and (= x2_5_0 x2_4_t)))
(assert (or (and (<= x2_4_t 20) (= mode_2_5 2))
            (and (> x2_4_t 20) (= mode_2_5 1))))
(assert (and (>= tau_5_0 0) (<= tau_5_0 1)
             (>= tau_5_t 0) (<= tau_5_t 1)
             (forall_t 1 [0 time_5] (>= tau_5_t 0))
             (forall_t 2 [0 time_5] (<= tau_5_t 1))))
(assert (and (not (and (= mode_1_5 1) (= mode_1_5 2)))
             (not (and (= mode_2_5 1) (= mode_2_5 2)))))            
(assert (or (and (= mode_1_5 2) (= mode_2_5 2)
                 (= [x1_5_t x2_5_t tau_5_t] 
                    (integral 0. time_5 [x1_5_0 x2_5_0 tau_5_0] flow_1)))
            (and (= mode_1_5 2) (= mode_2_5 1)
                 (= [x1_5_t x2_5_t tau_5_t] 
                    (integral 0. time_5 [x1_5_0 x2_5_0 tau_5_0] flow_2)))
            (and (= mode_1_5 1) (= mode_2_5 2)
                 (= [x1_5_t x2_5_t tau_5_t] 
                    (integral 0. time_5 [x1_5_0 x2_5_0 tau_5_0] flow_3)))
            (and (= mode_1_5 1) (= mode_2_5 1)
                 (= [x1_5_t x2_5_t tau_5_t] 
                    (integral 0. time_5 [x1_5_0 x2_5_0 tau_5_0] flow_4)))))
(assert (or (< x1_5_t (- 20 1)) (> x1_5_t (+ 20 1))))
(assert (or (< x2_5_t (- 20 1)) (> x2_5_t (+ 20 1))))
(check-sat)
(exit)
