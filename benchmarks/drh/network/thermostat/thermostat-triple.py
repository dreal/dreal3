
from gen import *

##########
# shared #
##########

flow_var[0] = """
(declare-fun tau () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
"""

flow_dec[0] = """
(define-ode flow_1 ((= d/dt[x1] (* 0.015 (- 100 (+ (* (- 1 0.03) x1) (* 0.01 x2) (* 0.02 x3)))))
                    (= d/dt[x2] (* 0.045 (- 200 (+ (* (- 1 0.06) x2) (* 0.01 x1) (* 0.05 x3)))))
                    (= d/dt[x3] (* 0.03 (- 300 (+ (* (- 1 0.07) x3) (* 0.02 x1) (* 0.05 x2)))))
		    (= d/dt[tau] 1)))
(define-ode flow_2 ((= d/dt[x1] (* 0.015 (- 100 (+ (* (- 1 0.03) x1) (* 0.01 x2) (* 0.02 x3)))))
                    (= d/dt[x2] (* 0.045 (- 200 (+ (* (- 1 0.06) x2) (* 0.01 x1) (* 0.05 x3)))))
                    (= d/dt[x3] (* -0.03 (+ (* (- 1 0.07) x3) (* 0.02 x1) (* 0.05 x2))))
		    (= d/dt[tau] 1)))
(define-ode flow_3 ((= d/dt[x1] (* 0.015 (- 100 (+ (* (- 1 0.03) x1) (* 0.01 x2) (* 0.02 x3))))) 
                    (= d/dt[x2] (* -0.045 (+ (* (- 1 0.06) x2) (* 0.01 x1) (* 0.05 x3))))
                    (= d/dt[x3] (* 0.03 (- 300 (+ (* (- 1 0.07) x3) (* 0.02 x1) (* 0.05 x2)))))
		    (= d/dt[tau] 1)))
(define-ode flow_4 ((= d/dt[x1] (* 0.015 (- 100 (+ (* (- 1 0.03) x1) (* 0.01 x2) (* 0.02 x3))))) 
                    (= d/dt[x2] (* -0.045 (+ (* (- 1 0.06) x2) (* 0.01 x1) (* 0.05 x3))))
                    (= d/dt[x3] (* -0.03 (+ (* (- 1 0.07) x3) (* 0.02 x1) (* 0.05 x2))))
		    (= d/dt[tau] 1)))
(define-ode flow_5 ((= d/dt[x1] (* -0.015 (+ (* (- 1 0.03) x1) (* 0.01 x2) (* 0.02 x3))))
                    (= d/dt[x2] (* 0.045 (- 200 (+ (* (- 1 0.06) x2) (* 0.01 x1) (* 0.05 x3)))))
                    (= d/dt[x3] (* 0.03 (- 300 (+ (* (- 1 0.07) x3) (* 0.02 x1) (* 0.05 x2)))))
		    (= d/dt[tau] 1)))
(define-ode flow_6 ((= d/dt[x1] (* -0.015 (+ (* (- 1 0.03) x1) (* 0.01 x2) (* 0.02 x3))))
                    (= d/dt[x2] (* 0.045 (- 200 (+ (* (- 1 0.06) x2) (* 0.01 x1) (* 0.05 x3)))))
                    (= d/dt[x3] (* -0.03 (+ (* (- 1 0.07) x3) (* 0.02 x1) (* 0.05 x2))))
		    (= d/dt[tau] 1)))
(define-ode flow_7 ((= d/dt[x1] (* -0.015 (+ (* (- 1 0.03) x1) (* 0.01 x2) (* 0.02 x3))))
                    (= d/dt[x2] (* -0.045 (+ (* (- 1 0.06) x2) (* 0.01 x1) (* 0.05 x3))))
                    (= d/dt[x3] (* 0.03 (- 300 (+ (* (- 1 0.07) x3) (* 0.02 x1) (* 0.05 x2)))))
		    (= d/dt[tau] 1)))
(define-ode flow_8 ((= d/dt[x1] (* -0.015 (+ (* (- 1 0.03) x1) (* 0.01 x2) (* 0.02 x3))))
                    (= d/dt[x2] (* -0.045 (+ (* (- 1 0.06) x2) (* 0.01 x1) (* 0.05 x3))))
                    (= d/dt[x3] (* -0.03 (+ (* (- 1 0.07) x3) (* 0.02 x1) (* 0.05 x2))))
		    (= d/dt[tau] 1)))
"""

state_dec[0] = """
(declare-fun time_{0} () Real)  
(declare-fun tau_{0}_0 () Real) 
(declare-fun tau_{0}_t () Real) 
(declare-fun mode_1_{0} () Int) 
(declare-fun x1_{0}_0 () Real)  
(declare-fun x1_{0}_t () Real)  
(declare-fun mode_2_{0} () Int)
(declare-fun x2_{0}_0 () Real)  
(declare-fun x2_{0}_t () Real)  
(declare-fun mode_3_{0} () Int)
(declare-fun x3_{0}_0 () Real)  
(declare-fun x3_{0}_t () Real)  
"""

state_val[0] = """
(assert (<= 0 time_{0}))  (assert (<= time_{0} 1))
(assert (<= 0 tau_{0}_0)) (assert (<= tau_{0}_0 1))
(assert (<= 0 tau_{0}_t)) (assert (<= tau_{0}_t 1))
(assert (<= -20 x1_{0}_0)) (assert (<= x1_{0}_0 100))
(assert (<= -20 x1_{0}_t)) (assert (<= x1_{0}_t 100))
(assert (<= -20 x2_{0}_0)) (assert (<= x2_{0}_0 100))
(assert (<= -20 x2_{0}_t)) (assert (<= x2_{0}_t 100))
(assert (<= -20 x3_{0}_0)) (assert (<= x3_{0}_0 100))
(assert (<= -20 x3_{0}_t)) (assert (<= x3_{0}_t 100))
(assert (<= 1 mode_1_{0})) (assert (<= mode_1_{0} 2)) (assert (not (and (= mode_1_{0} 1) (= mode_1_{0} 2))))
(assert (<= 1 mode_2_{0})) (assert (<= mode_2_{0} 2)) (assert (not (and (= mode_2_{0} 1) (= mode_2_{0} 2))))
(assert (<= 1 mode_3_{0})) (assert (<= mode_3_{0} 2)) (assert (not (and (= mode_3_{0} 1) (= mode_3_{0} 2))))
"""

cont_cond[0] = ["""
(assert (and (>= tau_{0}_0 0) (<= tau_{0}_0 1)
             (>= tau_{0}_t 0) (<= tau_{0}_t 1)
             (forall_t 1 [0 time_{0}] (>= tau_{0}_t 0))
             (forall_t 2 [0 time_{0}] (<= tau_{0}_t 1))))
(assert (or (and (= mode_1_{0} 2) (= mode_2_{0} 2) (= mode_3_{0} 2)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_1)))
            (and (= mode_1_{0} 2) (= mode_2_{0} 2) (= mode_3_{0} 1)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_2)))
            (and (= mode_1_{0} 2) (= mode_2_{0} 1) (= mode_3_{0} 2)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_3)))
            (and (= mode_1_{0} 2) (= mode_2_{0} 1) (= mode_3_{0} 1)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_4)))
            (and (= mode_1_{0} 1) (= mode_2_{0} 2) (= mode_3_{0} 2)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_5)))
            (and (= mode_1_{0} 1) (= mode_2_{0} 2) (= mode_3_{0} 1)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_6)))
            (and (= mode_1_{0} 1) (= mode_2_{0} 1) (= mode_3_{0} 2)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_7)))
            (and (= mode_1_{0} 1) (= mode_2_{0} 1) (= mode_3_{0} 1)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_8)))))"""]

jump_cond[0] = ["""
(assert (and (= tau_{0}_t 1) (= tau_{1}_0 0)))
(assert (and (= x1_{1}_0 x1_{0}_t)))
(assert (or (and (<= x1_{0}_t 20) (= mode1_{1} 2))
            (and (> x1_{0}_t 20) (= mode1_{1} 1))))
(assert (and (= x2_{1}_0 x2_{0}_t)))
(assert (or (and (<= x2_{0}_t 20) (= mode2_{1} 2))
            (and (> x2_{0}_t 20) (= mode2_{1} 1))))
(assert (and (= x3_{1}_0 x3_{0}_t)))
(assert (or (and (<= x3_{0}_t 20) (= mode3_{1} 2))
            (and (> x3_{0}_t 20) (= mode3_{1} 1))))"""]


#############
# Init/Goal #
#############

init_cond = """
(assert (= tau_{0}_0 0))
(assert (= mode1_{0} 2))
(assert (and (>= x1_{0}_0 (- 20 1)) (<= x1_{0}_0 (+ 20 1))))
(assert (= mode2_{0} 2))
(assert (and (>= x2_{0}_0 (- 20 1)) (<= x2_{0}_0 (+ 20 1))))
(assert (= mode3_{0} 2))
(assert (and (>= x3_{0}_0 (- 20 1)) (<= x3_{0}_0 (+ 20 1))))
"""

goal_cond = """
(assert (or (< x1_{0}_t (- 20 5)) (> x1_{0}_t (+ 20 5))))
(assert (or (< x2_{0}_t (- 20 5)) (> x2_{0}_t (+ 20 5))))
(assert (or (< x3_{0}_t (- 20 5)) (> x3_{0}_t (+ 20 5))))
"""

import sys
try:
    bound = int(sys.argv[1])
except:
    print("Usage:", sys.argv[0], "<Bound>")
else:
    generate(bound, 1, [0], 0, init_cond, goal_cond)

