
from gen import *

##########
# shared #
##########

flow_var[0] = """
(declare-fun tau () Real)
(declare-fun d1 () Real)
(declare-fun g1 () Real)
(declare-fun d2 () Real)
(declare-fun g2 () Real)
"""

flow_dec[0] = """
(define-ode flow_1 ((= d/dt[d1] (- (/ 0.5 0.166) (* 0.122 d1))) (= d/dt[g1] -0.5) (= d/dt[d2] (- (/ 0.5 0.166) (* 0.122 d2))) (= d/dt[g2] -0.5) (= d/dt[tau] 1)))
(define-ode flow_2 ((= d/dt[d1] (- (/ 1 0.166) (* 0.122 d1))) (= d/dt[g1] -1) (= d/dt[d2] (- 0 (* 0.122 d2))) (= d/dt[g2] 0) (= d/dt[tau] 1)))
(define-ode flow_3 ((= d/dt[d1] (- 0 (* 0.122 d1))) (= d/dt[g1] 0) (= d/dt[d2] (- (/ 1 0.166) (* 0.122 d2))) (= d/dt[g2] -1) (= d/dt[tau] 1)))
(define-ode flow_4 ((= d/dt[d1] 0) (= d/dt[g1] 0) (= d/dt[d2] (- (/ 1 0.166) (* 0.122 d2))) (= d/dt[g2] -1) (= d/dt[tau] 1)))
(define-ode flow_5 ((= d/dt[d1] (- (/ 1 0.166) (* 0.122 d1))) (= d/dt[g1] -1) (= d/dt[d2] 0) (= d/dt[g2] 0) (= d/dt[tau] 1)))
(define-ode flow_6 ((= d/dt[d1] 0) (= d/dt[g1] 0) (= d/dt[d2] 0) (= d/dt[g2] 0) (= d/dt[tau] 1)))
"""

state_dec[0] = """
(declare-fun time_{0} () Real)  
(declare-fun tau_{0}_0 () Real) 
(declare-fun tau_{0}_t () Real) 
(declare-fun mode_1_{0} () Int) 
(declare-fun d1_{0}_0 () Real)  
(declare-fun d1_{0}_t () Real)  
(declare-fun g1_{0}_0 () Real)  
(declare-fun g1_{0}_t () Real)  
(declare-fun mode_2_{0} () Int) 
(declare-fun d2_{0}_0 () Real)  
(declare-fun d2_{0}_t () Real)  
(declare-fun g2_{0}_0 () Real)  
(declare-fun g2_{0}_t () Real)  
"""

state_val[0] = """
(assert (<= 0 time_{0}))  (assert (<= time_{0} 20))
(assert (<= 0 tau_{0}_0)) (assert (<= tau_{0}_0 50))
(assert (<= 0 tau_{0}_t)) (assert (<= tau_{0}_t 50))
(assert (<= -10 d1_{0}_0)) (assert (<= d1_{0}_0 10))
(assert (<= -10 d1_{0}_t)) (assert (<= d1_{0}_t 10))
(assert (<= -10 g1_{0}_0)) (assert (<= g1_{0}_0 10))
(assert (<= -10 g1_{0}_t)) (assert (<= g1_{0}_t 10))
(assert (<= -10 d2_{0}_0)) (assert (<= d2_{0}_0 10))
(assert (<= -10 d2_{0}_t)) (assert (<= d2_{0}_t 10))
(assert (<= -10 g2_{0}_0)) (assert (<= g2_{0}_0 10))
(assert (<= -10 g2_{0}_t)) (assert (<= g2_{0}_t 10))
(assert (and (not (and (= mode_1_{0} 1) (= mode_1_{0} 2))) (not (and (= mode_1_{0} 1) (= mode_1_{0} 3))) (not (and (= mode_1_{0} 1) (= mode_1_{0} 4)))
             (not (and (= mode_1_{0} 2) (= mode_1_{0} 3))) (not (and (= mode_1_{0} 2) (= mode_1_{0} 4)))
             (not (and (= mode_1_{0} 3) (= mode_1_{0} 4)))))
(assert (and (not (and (= mode_2_{0} 1) (= mode_2_{0} 2))) (not (and (= mode_2_{0} 1) (= mode_2_{0} 3))) (not (and (= mode_2_{0} 1) (= mode_2_{0} 4)))
             (not (and (= mode_2_{0} 2) (= mode_2_{0} 3))) (not (and (= mode_2_{0} 2) (= mode_2_{0} 4)))
             (not (and (= mode_2_{0} 3) (= mode_2_{0} 4)))))
(assert (or 
  (and (= mode_1_{0} 4) (= mode_2_{0} 4))
  (and (= mode_1_{0} 3) (= mode_2_{0} 2))
  (and (= mode_1_{0} 3) (= mode_2_{0} 1))
  (and (= mode_1_{0} 2) (= mode_2_{0} 3))
  (and (= mode_1_{0} 1) (= mode_2_{0} 3))
  (and (= mode_1_{0} 1) (= mode_2_{0} 1))))
"""

cont_cond[0] = ["""
(assert (or
  (and (= mode_1_{0} 4) (= mode_2_{0} 4) 
       (= [d1_{0}_t g1_{0}_t g2_{0}_t d2_{0}_t tau_{0}_t] 
          (integral 0. time_{0} [d1_{0}_0 g1_{0}_0 g2_{0}_0 d2_{0}_0 tau_{0}_0] flow_1)))
  (and (= mode_1_{0} 3) (= mode_2_{0} 2)
       (= [d1_{0}_t g1_{0}_t g2_{0}_t d2_{0}_t tau_{0}_t] 
          (integral 0. time_{0} [d1_{0}_0 g1_{0}_0 g2_{0}_0 d2_{0}_0 tau_{0}_0] flow_2)))
  (and (= mode_1_{0} 2) (= mode_2_{0} 3)
       (= [d1_{0}_t g1_{0}_t g2_{0}_t d2_{0}_t tau_{0}_t] 
          (integral 0. time_{0} [d1_{0}_0 g1_{0}_0 g2_{0}_0 d2_{0}_0 tau_{0}_0] flow_3)))
  (and (= mode_1_{0} 1) (= mode_2_{0} 3)
       (= [d1_{0}_t g1_{0}_t g2_{0}_t d2_{0}_t tau_{0}_t] 
          (integral 0. time_{0} [d1_{0}_0 g1_{0}_0 g2_{0}_0 d2_{0}_0 tau_{0}_0] flow_4)))
  (and (= mode_1_{0} 3) (= mode_2_{0} 1)
       (= [d1_{0}_t g1_{0}_t g2_{0}_t d2_{0}_t tau_{0}_t] 
          (integral 0. time_{0} [d1_{0}_0 g1_{0}_0 g2_{0}_0 d2_{0}_0 tau_{0}_0] flow_5)))
  (and (= mode_1_{0} 1) (= mode_2_{0} 1)
       (= [d1_{0}_t g1_{0}_t g2_{0}_t d2_{0}_t tau_{0}_t] 
          (integral 0. time_{0} [d1_{0}_0 g1_{0}_0 g2_{0}_0 d2_{0}_0 tau_{0}_0] flow_6)))))
"""]

jump_cond[0] = ["""
(assert (= tau_{1}_0 tau_{0}_t))
(assert (and (= d1_{1}_0 d1_{0}_t) (= g1_{1}_0 g1_{0}_t)))
(assert (or (and (<= g1_0_t (* (- 1 0.166) d1_0_t)) 
                 (= mode_1_{1} 1))
            (and (>  g1_0_t (* (- 1 0.166) d1_0_t)) 
                 (not (and (= mode_1_{0} 1)))
	         (not (and (= mode_1_{1} 1))))))
(assert (and (= d2_{1}_0 d2_{0}_t) (= g2_{1}_0 g2_{0}_t)))
(assert (or (and (<= g2_0_t (* (- 1 0.166) d2_0_t)) 
                 (= mode_2_{1} 1))
            (and (>  g2_0_t (* (- 1 0.166) d2_0_t)) 
                 (not (and (= mode_2_{0} 1)))
	         (not (and (= mode_2_{1} 1))))))"""]

#############
# Init/Goal #
#############

init_cond = """
(assert (= tau_{0}_0 0))
(assert (and (= mode_1_{0} 4)))
(assert (and (= g1_{0}_0 8.5) (= d1_{0}_0 0)))
(assert (and (= mode_2_{0} 4)))
(assert (and (= g2_{0}_0 7.5) (= d2_{0}_0 0)))
"""

goal_cond = """
(assert (and (>= tau_{0}_t 10)
             (not (and (= mode_1_{0} 1) 
                       (= mode_2_{0} 1)))))
"""

import sys
try:
    bound = int(sys.argv[1])
except:
    print("Usage:", sys.argv[0], "<Bound>")
else:
    generate(bound, 1, [0], 3, init_cond, goal_cond)

