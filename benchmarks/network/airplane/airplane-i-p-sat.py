
from gen import *

########
# Main #
########

flow_var[0] = """
(declare-fun tau () Real)
(declare-fun r () Real)
(declare-fun psi () Real)
(declare-fun phi () Real)
(declare-fun p () Real)
(declare-fun gRDR () Real)
(declare-fun gAIL () Real)
(declare-fun beta () Real)
"""

flow_dec[0] = """
(define-ode flow_1 
  ((= d/dt[tau] 1)
   (= d/dt[r] (+ (+ (+ (+ (* 0.40742 beta) (* -0.056276 p)) (* -0.18801 r)) (* 0.005685 xAIL)) (* -0.106592 xRDR))) 
   (= d/dt[psi] (* (/ 9.80555 92.8277) phi)) 
   (= d/dt[phi] p) 
   (= d/dt[p] (+ (+ (+ (+ (* -1.70098 beta) (* -1.18465 p)) (* 0.223908 r)) (* 0.531304 xAIL)) (* 0.049766 xRDR))) 
   (= d/dt[gRDR] 0) 
   (= d/dt[gAIL] 0) 
   (= d/dt[beta] (+ (+ (- (* -0.099593 beta) r) (* (/ 9.80555 92.8277) phi)) (* 0.740361 xRDR)))))
"""

state_dec[0] = """
(declare-fun time_{0} () Real)  
(declare-fun tau_{0}_0 () Real) 
(declare-fun tau_{0}_t () Real) 
(declare-fun r_{0}_0 () Real)
(declare-fun r_{0}_t () Real)
(declare-fun psi_{0}_0 () Real)
(declare-fun psi_{0}_t () Real)
(declare-fun phi_{0}_0 () Real)
(declare-fun phi_{0}_t () Real)
(declare-fun p_{0}_0 () Real)
(declare-fun p_{0}_t () Real)
(declare-fun gRDR_{0}_0 () Real)
(declare-fun gRDR_{0}_t () Real)
(declare-fun gAIL_{0}_0 () Real)
(declare-fun gAIL_{0}_t () Real)
(declare-fun beta_{0}_0 () Real)
(declare-fun beta_{0}_t () Real)
"""

state_val[0] = """
(assert (<= 0 time_{0}))  (assert (<= time_{0} 1))
(assert (<= 0 tau_{0}_0)) (assert (<= tau_{0}_0 0.5))
(assert (<= 0 tau_{0}_t)) (assert (<= tau_{0}_t 0.5))
(assert (<= -3.14159 r_{0}_0)) (assert (<= r_{0}_0 3.14159))
(assert (<= -3.14159 r_{0}_t)) (assert (<= r_{0}_t 3.14159))
(assert (<= -3.14159 psi_{0}_0)) (assert (<= psi_{0}_0 3.14159))
(assert (<= -3.14159 psi_{0}_t)) (assert (<= psi_{0}_t 3.14159))
(assert (<= -3.14159 phi_{0}_0)) (assert (<= phi_{0}_0 3.14159))
(assert (<= -3.14159 phi_{0}_t)) (assert (<= phi_{0}_t 3.14159))
(assert (<= -3.14159 p_{0}_0)) (assert (<= p_{0}_0 3.14159))
(assert (<= -3.14159 p_{0}_t)) (assert (<= p_{0}_t 3.14159))
(assert (<= -3.14159 gRDR_{0}_0)) (assert (<= gRDR_{0}_0 3.14159))
(assert (<= -3.14159 gRDR_{0}_t)) (assert (<= gRDR_{0}_t 3.14159))
(assert (<= -3.14159 gAIL_{0}_0)) (assert (<= gAIL_{0}_0 3.14159))
(assert (<= -3.14159 gAIL_{0}_t)) (assert (<= gAIL_{0}_t 3.14159))
(assert (<= -3.14159 beta_{0}_0)) (assert (<= beta_{0}_0 3.14159))
(assert (<= -3.14159 beta_{0}_t)) (assert (<= beta_{0}_t 3.14159))
"""

# 4 steps (1/3, 1/2, 2/3, 1) * 0.5
cont_cond[0] = [
"""
(assert (and (>= tau_{0}_0 0) (<= tau_{0}_0 (/ 0.5 3))
             (>= tau_{0}_t 0) (<= tau_{0}_t (/ 0.5 3))))
(assert (and (= [xRDR_{0}_t xAIL_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                 phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                (pintegral 0. time_{0} 
                   [xRDR_{0}_0 xAIL_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                    phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] 
                   [holder_{1} holder_{2} holder_{3}]))
             (connect holder_{3} flow_1)))""",
"""
(assert (and (>= tau_{0}_0 (/ 0.5 3)) (<= tau_{0}_0 (/ 0.5 2))
             (>= tau_{0}_t (/ 0.5 3)) (<= tau_{0}_t (/ 0.5 2))))
(assert (and (= [xRDR_{0}_t xAIL_{0}_t tau_{0}_t r_{0}_t psi_{0}_t 
                 phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t] 
                (pintegral 0. time_{0} 
                   [xRDR_{0}_0 xAIL_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                    phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0]
                   [holder_{1} holder_{2} holder_{3}]))
             (connect holder_{3} flow_1)))""",
"""
(assert (and (>= tau_{0}_0 (/ 0.5 2)) (<= tau_{0}_0 (/ 1 3))
             (>= tau_{0}_t (/ 0.5 2)) (<= tau_{0}_t (/ 1 3))))
(assert (and (= [xRDR_{0}_t xAIL_{0}_t tau_{0}_t r_{0}_t psi_{0}_t 
                 phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t] 
                (pintegral 0. time_{0} 
                   [xRDR_{0}_0 xAIL_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                    phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0]
                   [holder_{1} holder_{2} holder_{3}]))
             (connect holder_{3} flow_1)))""",
"""
(assert (and (>= tau_{0}_0 (/ 1 3)) (<= tau_{0}_0 0.5)
             (>= tau_{0}_t (/ 1 3)) (<= tau_{0}_t 0.5)))
(assert (and (= [xRDR_{0}_t xAIL_{0}_t tau_{0}_t r_{0}_t psi_{0}_t 
                 phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t] 
                (pintegral 0. time_{0} 
                   [xRDR_{0}_0 xAIL_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                    phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] 
                   [holder_{1} holder_{2} holder_{3}]))
             (connect holder_{3} flow_1)))"""]

# 4 steps (1/3, 1/2, 2/3, 1) * 0.5
jump_cond[0] = [
"""
(assert (and (= tau_{0}_t (/ 0.5 3))   (= tau_{1}_0 tau_{0}_t) 
             (= gRDR_{1}_0 gRDR_{0}_t) (= gAIL_{1}_0 gAIL_{0}_t) 
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t)   
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t)       
             (= beta_{1}_0 beta_{0}_t)))""",
"""
(assert (and (= tau_{0}_t (/ 0.5 2))   (= tau_{1}_0 tau_{0}_t)
             (= gRDR_{1}_0 gRDR_{0}_t) (= gAIL_{1}_0 gAIL_{0}_t) 
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t)   
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t)     
             (= beta_{1}_0 beta_{0}_t)))""",
"""
(assert (and (= tau_{0}_t (/ 1 3))     (= tau_{1}_0 tau_{0}_t)
             (= gRDR_{1}_0 gRDR_{0}_t) (= gAIL_{1}_0 gAIL_{0}_t) 
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t)   
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t)     
             (= beta_{1}_0 beta_{0}_t)))""",
"""
(assert (and (= tau_{0}_t 0.5)         (= tau_{1}_0 0)
             (= gRDR_{1}_0 gRDR_{0}_t) (= gAIL_{1}_0 gAIL_{0}_t)
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t) 
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t) 
             (= beta_{1}_0 beta_{0}_t)))"""]

###########
# Aileron #
###########

flow_var[1] = """
(declare-fun xAIL () Real)
"""

flow_dec[1] = """
(define-ode flow_2 ((= d/dt[xAIL] 0.25)))
(define-ode flow_3 ((= d/dt[xAIL] -0.25)))
"""

state_dec[1] = """
(declare-fun mode_1_{0} () Int) 
(declare-fun xAIL_{0}_0 () Real)
(declare-fun xAIL_{0}_t () Real)
"""

state_val[1] = """
(assert (<= -3.14159 xAIL_{0}_0)) (assert (<= xAIL_{0}_0 3.14159))
(assert (<= -3.14159 xAIL_{0}_t)) (assert (<= xAIL_{0}_t 3.14159))
"""

# 4 steps (1/3, 1/2, 2/3, 1) * 0.5
cont_cond[1] = ["""
(assert (or (not (= mode_1_{0} 1)) (not (= mode_1_{0} 2))))
(assert (or (not (= mode_1_{1} 1)) (not (= mode_1_{1} 2))))
(assert (or (not (= mode_2_{0} 2)) (not (= mode_2_{0} 1))))
(assert (or (not (= mode_2_{1} 2)) (not (= mode_2_{1} 1))))

(assert (or (and (= mode_1_{0} 2)  (connect holder_{1} flow_2))
            (and (= mode_1_{0} 1) (connect holder_{1} flow_3))))
(assert (not (and (connect holder_{1} flow_2)  (connect holder_{1} flow_3))))""",
"""
(assert (or (and (= mode_1_{0} 2)  (connect holder_{1} flow_2))
            (and (= mode_1_{0} 1) (connect holder_{1} flow_3))))
(assert (not (and (connect holder_{1} flow_2)  (connect holder_{1} flow_3))))""",
"""
(assert (or (and (= mode_1_{0} 2)  (connect holder_{1} flow_2))
            (and (= mode_1_{0} 1) (connect holder_{1} flow_3))))
(assert (not (and (connect holder_{1} flow_2) (connect holder_{1} flow_3))))""",
"""
(assert (or (and (= mode_1_{0} 2)  (connect holder_{1} flow_2))
            (and (= mode_1_{0} 1) (connect holder_{1} flow_3))))
(assert (not (and (connect holder_{1} flow_2) (connect holder_{1} flow_3))))"""]

# 4 steps (1/3, 1/2, 2/3, 1) * 0.5
jump_cond[1] = ["""
(assert (= xAIL_{1}_0 xAIL_{0}_t))
(assert (= mode_1_{1} mode_1_{0}))""",
"""
(assert (= xAIL_{1}_0 xAIL_{0}_t))
(assert (or (and (>= gAIL_{0}_t xAIL_{0}_t) (= mode_1_{1} 2))
            (and (<  gAIL_{0}_t xAIL_{0}_t) (= mode_1_{1} 1))))""",
"""
(assert (= xAIL_{1}_0 xAIL_{0}_t))
(assert (= mode_1_{1} mode_1_{0}))""",
"""
(assert (and (= xAIL_{1}_0 xAIL_{0}_t)))
(assert (or (and (>= gAIL_{0}_t xAIL_{0}_t) (= mode_1_{1} 2))
            (and (<  gAIL_{0}_t xAIL_{0}_t) (= mode_1_{1} 1))))"""]

##########
# Rudder #
##########

flow_var[2] = """
(declare-fun xRDR () Real)
"""

flow_dec[2] = """
(define-ode flow_4 ((= d/dt[xRDR] 0.5)))
(define-ode flow_5 ((= d/dt[xRDR] -0.5)))
"""

state_dec[2] = """
(declare-fun mode_2_{0} () Int)
(declare-fun xRDR_{0}_0 () Real)
(declare-fun xRDR_{0}_t () Real)
"""

state_val[2] = """
(assert (<= -3.14159 xRDR_{0}_0)) (assert (<= xRDR_{0}_0 3.14159))
(assert (<= -3.14159 xRDR_{0}_t)) (assert (<= xRDR_{0}_t 3.14159))
"""

# 4 steps (1/3, 1/2, 2/3, 1) * 0.5
cont_cond[2] = ["""
(assert (or (and (= mode_2_{0} 2)  (connect holder_{2} flow_4))
            (and (= mode_2_{0} 1) (connect holder_{2} flow_5))))
(assert (not (and (connect holder_{2} flow_4)  (connect holder_{2} flow_5))))""",
"""
(assert (or (and (= mode_2_{0} 2)  (connect holder_{2} flow_4))
            (and (= mode_2_{0} 1) (connect holder_{2} flow_5))))
(assert (not (and (connect holder_{2} flow_4)  (connect holder_{2} flow_5))))""",
"""
(assert (or (and (= mode_2_{0} 2)  (connect holder_{2} flow_4))
            (and (= mode_2_{0} 1) (connect holder_{2} flow_5))))
(assert (not (and (connect holder_{2} flow_4) (connect holder_{2} flow_5))))""",
"""
(assert (or (and (= mode_2_{0} 2)  (connect holder_{2} flow_4))
            (and (= mode_2_{0} 1) (connect holder_{2} flow_5))))
(assert (not (and (connect holder_{2} flow_4) (connect holder_{2} flow_5))))"""]
           

# 4 steps (1/3, 1/2, 2/3, 1) * 0.5
jump_cond[2] = ["""
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (or (and (>= gRDR_{0}_t xRDR_{0}_t) (= mode_2_{1} 2))
            (and (<  gRDR_{0}_t xRDR_{0}_t) (= mode_2_{1} 1))))""", 
"""
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (= mode_2_{1} mode_2_{0}))""", 
"""
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (or (and (>= gRDR_{0}_t xRDR_{0}_t) (= mode_2_{1} 2))
            (and (<  gRDR_{0}_t xRDR_{0}_t) (= mode_2_{1} 1))))""", 
"""
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (or (and (>= gRDR_{0}_t xRDR_{0}_t) (= mode_2_{1} 2))
            (and (<  gRDR_{0}_t xRDR_{0}_t) (= mode_2_{1} 1))))"""] 



#############
# Init/Goal #
#############

init_cond = """
(assert (and (= tau_{0}_0 0)  (= gRDR_{0}_0 0) (= gAIL_{0}_0 0) (= psi_{0}_0 0) 
             (= phi_{0}_0 0)  (= r_{0}_0 0)    (= p_{0}_0 0)    (= beta_{0}_0 0)))
(assert (and (= xAIL_{0}_0 0) (= mode_1_{0} 2)))
(assert (and (= xRDR_{0}_0 0) (= mode_2_{0} 2)))
"""

goal_cond = """
(assert (< (^ (^ beta_{0}_t 2) 0.5) 0.1))
"""

import sys
try:
    bound = int(sys.argv[1])
except:
    print("Usage:", sys.argv[0], "<Bound>")
else:
    generate(bound, 4, [0,1,2], 3, init_cond, goal_cond)

