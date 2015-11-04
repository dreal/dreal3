
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
(declare-fun xAIL () Real)
(declare-fun xRDR () Real)
"""

flow_dec[0] = """
(define-ode flow_1 ((= d/dt[beta] (+ (- (/ (* (* 13.97 300) (+ (+ (* (/ (* -0.02 180) 3.14159) beta) (/ (* 0.021 xAIL) 20)) (/ (* 0.086 xRDR) 30))) (* 20500 111.64)) r) (* (* (/ 111.64 9.80555) (cos beta)) (sin phi)))) (= d/dt[p] (+ (* (* (+ (* -0.77 r) (* 0.02755 p)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 0.0001055 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.642e-06 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30))))))) (= d/dt[r] (+ (* (* (- (* -0.7336 p) (* 0.02755 r)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 1.642e-06 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.587e-05 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30))))))) (= d/dt[phi] p) (= d/dt[psi] (* (/ 9.80555 111.64) (/ (sin phi) (cos phi)))) (= d/dt[xAIL] 0.25) (= d/dt[xRDR] 0.5) (= d/dt[gAIL] 0) (= d/dt[gRDR] 0) (= d/dt[gDir] 0) (= d/dt[tau] 1)))
(define-ode flow_2 ((= d/dt[beta] (+ (- (/ (* (* 13.97 300) (+ (+ (* (/ (* -0.02 180) 3.14159) beta) (/ (* 0.021 xAIL) 20)) (/ (* 0.086 xRDR) 30))) (* 20500 111.64)) r) (* (* (/ 111.64 9.80555) (cos beta)) (sin phi)))) (= d/dt[p] (+ (* (* (+ (* -0.77 r) (* 0.02755 p)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 0.0001055 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.642e-06 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30))))))) (= d/dt[r] (+ (* (* (- (* -0.7336 p) (* 0.02755 r)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 1.642e-06 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.587e-05 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30))))))) (= d/dt[phi] p) (= d/dt[psi] (* (/ 9.80555 111.64) (/ (sin phi) (cos phi)))) (= d/dt[xAIL] 0.25) (= d/dt[xRDR] -0.5) (= d/dt[gAIL] 0) (= d/dt[gRDR] 0) (= d/dt[gDir] 0) (= d/dt[tau] 1)))
(define-ode flow_3 ((= d/dt[beta] (+ (- (/ (* (* 13.97 300) (+ (+ (* (/ (* -0.02 180) 3.14159) beta) (/ (* 0.021 xAIL) 20)) (/ (* 0.086 xRDR) 30))) (* 20500 111.64)) r) (* (* (/ 111.64 9.80555) (cos beta)) (sin phi)))) (= d/dt[p] (+ (* (* (+ (* -0.77 r) (* 0.02755 p)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 0.0001055 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.642e-06 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30))))))) (= d/dt[r] (+ (* (* (- (* -0.7336 p) (* 0.02755 r)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 1.642e-06 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.587e-05 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30))))))) (= d/dt[phi] p) (= d/dt[psi] (* (/ 9.80555 111.64) (/ (sin phi) (cos phi)))) (= d/dt[xAIL] -0.25) (= d/dt[xRDR] 0.5) (= d/dt[gAIL] 0) (= d/dt[gRDR] 0) (= d/dt[gDir] 0) (= d/dt[tau] 1)))
(define-ode flow_4 ((= d/dt[beta] (+ (- (/ (* (* 13.97 300) (+ (+ (* (/ (* -0.02 180) 3.14159) beta) (/ (* 0.021 xAIL) 20)) (/ (* 0.086 xRDR) 30))) (* 20500 111.64)) r) (* (* (/ 111.64 9.80555) (cos beta)) (sin phi)))) (= d/dt[p] (+ (* (* (+ (* -0.77 r) (* 0.02755 p)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 0.0001055 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.642e-06 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30))))))) (= d/dt[r] (+ (* (* (- (* -0.7336 p) (* 0.02755 r)) r) (/ (sin phi) (cos phi))) (* (* (* 13.97 30) 300) (+ (* 1.642e-06 (+ (+ (* (/ (* -0.0008 180) 3.14159) beta) (/ (* 0.05 xAIL) 20)) (/ (* 0.013 xRDR) 30))) (* 1.587e-05 (+ (+ (* (/ (* 0.02 180) 3.14159) beta) (/ (* -0.01 xAIL) 20)) (/ (* -0.04 xRDR) 30))))))) (= d/dt[phi] p) (= d/dt[psi] (* (/ 9.80555 111.64) (/ (sin phi) (cos phi)))) (= d/dt[xAIL] -0.25) (= d/dt[xRDR] -0.5) (= d/dt[gAIL] 0) (= d/dt[gRDR] 0) (= d/dt[gDir] 0) (= d/dt[tau] 1)))
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
(declare-fun modeA_{0} () Bool) 
(declare-fun xAIL_{0}_0 () Real)
(declare-fun xAIL_{0}_t () Real)
(declare-fun modeR_{0} () Bool)
(declare-fun xRDR_{0}_0 () Real)
(declare-fun xRDR_{0}_t () Real)
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
(assert (<= -3.14159 xAIL_{0}_0)) (assert (<= xAIL_{0}_0 3.14159))
(assert (<= -3.14159 xAIL_{0}_t)) (assert (<= xAIL_{0}_t 3.14159))
(assert (<= -3.14159 xRDR_{0}_0)) (assert (<= xRDR_{0}_0 3.14159))
(assert (<= -3.14159 xRDR_{0}_t)) (assert (<= xRDR_{0}_t 3.14159))
"""

cont_cond[0] = [
"""
(assert (and (>= tau_{0}_0 0) (<= tau_{0}_0 0.5)
             (>= tau_{0}_t 0) (<= tau_{0}_t 0.5)))
(assert (or (and (= modeA_{0} true) (= modeR_{0} true)
                 (= [beta_{0}_t p_{0}_t r_{0}_t phi_{0}_t psi_{0}_t xAIL_{0}_t xRDR_{0}_t gAIL_{0}_t gRDR_{0}_t gDir_{0}_t tau_{0}_t]
                    (integral 0. time_{0} 
		       [beta_{0}_0 p_{0}_0 r_{0}_0 phi_{0}_0 psi_{0}_0 xAIL_{0}_0 xRDR_{0}_0 gAIL_{0}_0 gRDR_{0}_0 gDir_{0}_0 tau_{0}_0] flow_1)))
            (and (= modeA_{0} true) (= modeR_{0} false)
                 (= [beta_{0}_t p_{0}_t r_{0}_t phi_{0}_t psi_{0}_t xAIL_{0}_t xRDR_{0}_t gAIL_{0}_t gRDR_{0}_t gDir_{0}_t tau_{0}_t]
                    (integral 0. time_{0} 
		       [beta_{0}_0 p_{0}_0 r_{0}_0 phi_{0}_0 psi_{0}_0 xAIL_{0}_0 xRDR_{0}_0 gAIL_{0}_0 gRDR_{0}_0 gDir_{0}_0 tau_{0}_0] flow_2)))
            (and (= modeA_{0} false) (= modeR_{0} true)
                 (= [beta_{0}_t p_{0}_t r_{0}_t phi_{0}_t psi_{0}_t xAIL_{0}_t xRDR_{0}_t gAIL_{0}_t gRDR_{0}_t gDir_{0}_t tau_{0}_t]
                    (integral 0. time_{0} 
		       [beta_{0}_0 p_{0}_0 r_{0}_0 phi_{0}_0 psi_{0}_0 xAIL_{0}_0 xRDR_{0}_0 gAIL_{0}_0 gRDR_{0}_0 gDir_{0}_0 tau_{0}_0] flow_3)))
            (and (= modeA_{0} false) (= modeR_{0} false)
                 (= [beta_{0}_t p_{0}_t r_{0}_t phi_{0}_t psi_{0}_t xAIL_{0}_t xRDR_{0}_t gAIL_{0}_t gRDR_{0}_t gDir_{0}_t tau_{0}_t]
                    (integral 0. time_{0} 
		       [beta_{0}_0 p_{0}_0 r_{0}_0 phi_{0}_0 psi_{0}_0 xAIL_{0}_0 xRDR_{0}_0 gAIL_{0}_0 gRDR_{0}_0 gDir_{0}_0 tau_{0}_0] flow_4)))))
"""]


jump_cond[0] = [
"""
(assert (and (= tau_{0}_t 0.5)         (= tau_{1}_0 0)
             (= gRDR_{1}_0 (* beta_{0}_t 0.35))
             (= gAIL_{1}_0 (* (- gDir_{0}_t (/ (* psi_{0}_t 180) 3.14)) 0.5))
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t) 
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t) 
             (= gDir_{1}_0 gDir_{0}_t) (= beta_{1}_0 beta_{0}_t)))
(assert (and (= xAIL_{1}_0 xAIL_{0}_t)))
(assert (or (and (>= gAIL_{0}_t xAIL_{0}_t) (= modeA_{1} true))
            (and (<  gAIL_{0}_t xAIL_{0}_t) (= modeA_{1} false))))
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (or (and (>= gRDR_{0}_t xRDR_{0}_t) (= modeR_{1} true))
            (and (<  gRDR_{0}_t xRDR_{0}_t) (= modeR_{1} false))))"""] 


#############
# Init/Goal #
#############

init_cond = """
(assert (and (= tau_{0}_0 0)  (= gRDR_{0}_0 0) (= gAIL_{0}_0 0) (= psi_{0}_0 0) 
             (= phi_{0}_0 0)  (= r_{0}_0 0)    (= p_{0}_0 0)    (= beta_{0}_0 0)
	     (< 0.5 gDir_{0}_0) (< gDir_{0}_0 0.7)))
(assert (and (= xAIL_{0}_0 0) (= modeA_{0} true)))
(assert (and (= xRDR_{0}_0 0) (= modeR_{0} true)))
"""

goal_cond = """
(assert (< (^ (^ beta_{0}_t 2) 0.5) 1))
"""

import sys
try:
    bound = int(sys.argv[1])
except:
    print("Usage:", sys.argv[0], "<Bound>")
else:
    generate(bound, 1, [0], 0, init_cond, goal_cond)

