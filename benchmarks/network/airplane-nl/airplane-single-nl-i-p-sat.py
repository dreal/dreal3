
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
(declare-fun gDir () Real)
(declare-fun beta () Real)
"""

flow_dec[0] = """
(define-ode flow_1 
  ((= d/dt[tau] 1)
   (= d/dt[r] (+ (* (* (- (* -0.7336 p) (* 0.02755 r)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 1.642e-06 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.587e-05 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30)))))))
   (= d/dt[psi] (* (/ 9.80555 111.64) (/ (sin phi) (cos phi))))
   (= d/dt[phi] p)
   (= d/dt[p] (+ (* (* (+ (* -0.77 r) (* 0.02755 p)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 0.0001055 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.642e-06 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30)))))))
   (= d/dt[gAIL] 0)
   (= d/dt[gRDR] 0)
   (= d/dt[gDir] 0)
   (= d/dt[beta] (+ (- (/ (* (* 13.97 300) (+ (+ (* (/ (* -0.02 180) 3.14159) beta) (/ (* 0.021 xAIL) 20)) (/ (* 0.086 xRDR) 30))) (* 20500 111.64)) r) (* (* (/ 111.64 9.80555) (cos beta)) (sin phi))))))
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
(declare-fun gDir_{0}_0 () Real)
(declare-fun gDir_{0}_t () Real)
(declare-fun beta_{0}_0 () Real)
(declare-fun beta_{0}_t () Real)
"""

state_val[0] = """
(assert (<= 0 time_{0}))  (assert (<= time_{0} 1))
(assert (<= 0 tau_{0}_0)) (assert (<= tau_{0}_0 0.5))
(assert (<= 0 tau_{0}_t)) (assert (<= tau_{0}_t 0.5))
(assert (<= -1.5 r_{0}_0)) (assert (<= r_{0}_0 1.5))
(assert (<= -1.5 r_{0}_t)) (assert (<= r_{0}_t 1.5))
(assert (<= -1.5 psi_{0}_0)) (assert (<= psi_{0}_0 1.5))
(assert (<= -1.5 psi_{0}_t)) (assert (<= psi_{0}_t 1.5))
(assert (<= -1.5 phi_{0}_0)) (assert (<= phi_{0}_0 1.5))
(assert (<= -1.5 phi_{0}_t)) (assert (<= phi_{0}_t 1.5))
(assert (<= -1.5 p_{0}_0)) (assert (<= p_{0}_0 1.5))
(assert (<= -1.5 p_{0}_t)) (assert (<= p_{0}_t 1.5))
(assert (<= -3.14159 gRDR_{0}_0)) (assert (<= gRDR_{0}_0 3.14159))
(assert (<= -3.14159 gRDR_{0}_t)) (assert (<= gRDR_{0}_t 3.14159))
(assert (<= -3.14159 gAIL_{0}_0)) (assert (<= gAIL_{0}_0 3.14159))
(assert (<= -3.14159 gAIL_{0}_t)) (assert (<= gAIL_{0}_t 3.14159))
(assert (<= -3.14159 gDir_{0}_0)) (assert (<= gDir_{0}_0 3.14159))
(assert (<= -3.14159 gDir_{0}_t)) (assert (<= gDir_{0}_t 3.14159))
(assert (<= -3.14159 beta_{0}_0)) (assert (<= beta_{0}_0 3.14159))
(assert (<= -3.14159 beta_{0}_t)) (assert (<= beta_{0}_t 3.14159))
"""

cont_cond[0] = [
"""
(assert (and (>= tau_{0}_0 0) (<= tau_{0}_0 0.5)
             (>= tau_{0}_t 0) (<= tau_{0}_t 0.5) ))
(assert (and (= [xRDR_{0}_t xAIL_{0}_t tau_{0}_t r_{0}_t psi_{0}_t 
                 phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t gDir_{0}_t beta_{0}_t] 
                (pintegral 0. time_{0} 
                   [xRDR_{0}_0 xAIL_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                    phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 gDir_{0}_0 beta_{0}_0] 
                   [holder_{1} holder_{2} holder_{3}]))
             (connect holder_{3} flow_1)))"""]

jump_cond[0] = [
"""
(assert (and (= tau_{0}_t 0.5)         (= tau_{1}_0 0)
             (= gRDR_{1}_0 (* beta_{0}_t 0.35))
             (= gAIL_{1}_0 (* (- gDir_{0}_t (/ (* psi_{0}_t 180) 3.14)) 0.5))
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t) 
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t) 
	     (= gDir_{1}_0 gDir_{0}_t) (= beta_{1}_0 beta_{0}_t)))"""]

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

cont_cond[1] = ["""
(assert (or (not (= mode_1_{0} 1)) (not (= mode_1_{0} 2))))
(assert (or (not (= mode_2_{0} 2)) (not (= mode_2_{0} 1))))

(assert (or (and (= mode_1_{0} 2)  (connect holder_{1} flow_2))
            (and (= mode_1_{0} 1) (connect holder_{1} flow_3))))
(assert (not (and (connect holder_{1} flow_2) (connect holder_{1} flow_3))))"""]

jump_cond[1] = ["""
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

cont_cond[2] = ["""
(assert (or (and (= mode_2_{0} 2)  (connect holder_{2} flow_4))
            (and (= mode_2_{0} 1) (connect holder_{2} flow_5))))
(assert (not (and (connect holder_{2} flow_4) (connect holder_{2} flow_5))))"""]
           

jump_cond[2] = ["""
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (or (and (>= gRDR_{0}_t xRDR_{0}_t) (= mode_2_{1} 2))
            (and (<  gRDR_{0}_t xRDR_{0}_t) (= mode_2_{1} 1))))"""] 



#############
# Init/Goal #
#############

init_cond = """
(assert (and (= tau_{0}_0 0)  (= gRDR_{0}_0 0) (= gAIL_{0}_0 0) (= psi_{0}_0 0) 
             (= phi_{0}_0 0)  (= r_{0}_0 0)    (= p_{0}_0 0)    (= beta_{0}_0 0)
	     (< 0.5 gDir_{0}_0) (< gDir_{0}_0 0.7)))
(assert (and (= xAIL_{0}_0 0) (= mode_1_{0} 2)))
(assert (and (= xRDR_{0}_0 0) (= mode_2_{0} 2)))
"""

goal_cond = """
(assert (< (^ (^ beta_{0}_t 2) 0.5) 0.2))
"""

import sys
try:
    bound = int(sys.argv[1])
except:
    print("Usage:", sys.argv[0], "<Bound>")
else:
    generate(bound, 1, [0,1,2], 3, init_cond, goal_cond)

