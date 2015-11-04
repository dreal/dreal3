
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
(declare-fun xAIL () Real)
(declare-fun xRDR () Real)
"""

flow_dec[0] = """
(define-ode flow_1 
  ((= d/dt[xAIL] 0.25)
   (= d/dt[xRDR] 0.5)
   (= d/dt[tau] 1)
   (= d/dt[r] (+ (+ (+ (+ (* 0.40742 beta) (* -0.056276 p)) (* -0.18801 r)) (* 0.005685 xAIL)) (* -0.106592 xRDR))) 
   (= d/dt[psi] (* (/ 9.80555 92.8277) phi)) 
   (= d/dt[phi] p) 
   (= d/dt[p] (+ (+ (+ (+ (* -1.70098 beta) (* -1.18465 p)) (* 0.223908 r)) (* 0.531304 xAIL)) (* 0.049766 xRDR))) 
   (= d/dt[gRDR] 0) 
   (= d/dt[gAIL] 0) 
   (= d/dt[beta] (+ (+ (- (* -0.099593 beta) r) (* (/ 9.80555 92.8277) phi)) (* 0.740361 xRDR)))))
(define-ode flow_2 
  ((= d/dt[xAIL] 0.25)
   (= d/dt[xRDR] -0.5)
   (= d/dt[tau] 1)
   (= d/dt[r] (+ (+ (+ (+ (* 0.40742 beta) (* -0.056276 p)) (* -0.18801 r)) (* 0.005685 xAIL)) (* -0.106592 xRDR))) 
   (= d/dt[psi] (* (/ 9.80555 92.8277) phi)) 
   (= d/dt[phi] p) 
   (= d/dt[p] (+ (+ (+ (+ (* -1.70098 beta) (* -1.18465 p)) (* 0.223908 r)) (* 0.531304 xAIL)) (* 0.049766 xRDR))) 
   (= d/dt[gRDR] 0) 
   (= d/dt[gAIL] 0) 
   (= d/dt[beta] (+ (+ (- (* -0.099593 beta) r) (* (/ 9.80555 92.8277) phi)) (* 0.740361 xRDR)))))
(define-ode flow_3 
  ((= d/dt[xAIL] -0.25)
   (= d/dt[xRDR] 0.5)
   (= d/dt[tau] 1)
   (= d/dt[r] (+ (+ (+ (+ (* 0.40742 beta) (* -0.056276 p)) (* -0.18801 r)) (* 0.005685 xAIL)) (* -0.106592 xRDR))) 
   (= d/dt[psi] (* (/ 9.80555 92.8277) phi)) 
   (= d/dt[phi] p) 
   (= d/dt[p] (+ (+ (+ (+ (* -1.70098 beta) (* -1.18465 p)) (* 0.223908 r)) (* 0.531304 xAIL)) (* 0.049766 xRDR))) 
   (= d/dt[gRDR] 0) 
   (= d/dt[gAIL] 0) 
   (= d/dt[beta] (+ (+ (- (* -0.099593 beta) r) (* (/ 9.80555 92.8277) phi)) (* 0.740361 xRDR)))))
(define-ode flow_4 
  ((= d/dt[xAIL] -0.25)
   (= d/dt[xRDR] -0.5)
   (= d/dt[tau] 1)
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
(assert (<= -3.14159 xAIL_{0}_0)) (assert (<= xAIL_{0}_0 3.14159))
(assert (<= -3.14159 xAIL_{0}_t)) (assert (<= xAIL_{0}_t 3.14159))
(assert (<= -3.14159 xRDR_{0}_0)) (assert (<= xRDR_{0}_0 3.14159))
(assert (<= -3.14159 xRDR_{0}_t)) (assert (<= xRDR_{0}_t 3.14159))
"""

# 4 steps (1/3, 1/2, 2/3, 1) * 0.5
cont_cond[0] = [
"""
(assert (and (>= tau_{0}_0 0) (<= tau_{0}_0 (/ 0.5 3))
             (>= tau_{0}_t 0) (<= tau_{0}_t (/ 0.5 3))
             (forall_t 1 [0 time_{0}] (>= tau_{0}_t 0)) 
             (forall_t 1 [0 time_{0}] (<= tau_{0}_t (/ 0.5 3)))))
(assert (or (and (= modeA_{0} true) (= modeR_{0} true)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_1)))
            (and (= modeA_{0} true) (= modeR_{0} false)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_2)))
            (and (= modeA_{0} false) (= modeR_{0} true)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_3)))
            (and (= modeA_{0} false) (= modeR_{0} false)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_4)))))
""",
"""
(assert (and (>= tau_{0}_0 (/ 0.5 3)) (<= tau_{0}_0 (/ 0.5 2))
             (>= tau_{0}_t (/ 0.5 3)) (<= tau_{0}_t (/ 0.5 2))
             (forall_t 5 [0 time_{0}] (>= tau_{0}_t (/ 0.5 3)))
             (forall_t 5 [0 time_{0}] (<= tau_{0}_t (/ 0.5 2)))))
(assert (or (and (= modeA_{0} true) (= modeR_{0} true)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_1)))
            (and (= modeA_{0} true) (= modeR_{0} false)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_2)))
            (and (= modeA_{0} false) (= modeR_{0} true)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_3)))
            (and (= modeA_{0} false) (= modeR_{0} false)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_4)))))
""",
"""
(assert (and (>= tau_{0}_0 (/ 0.5 2)) (<= tau_{0}_0 (/ 1 3))
             (>= tau_{0}_t (/ 0.5 2)) (<= tau_{0}_t (/ 1 3)) 
             (forall_t 9 [0 time_{0}] (>= tau_{0}_t (/ 0.5 2))) 
             (forall_t 9 [0 time_{0}] (<= tau_{0}_t (/ 1 3)))))
(assert (or (and (= modeA_{0} true) (= modeR_{0} true)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_1)))
            (and (= modeA_{0} true) (= modeR_{0} false)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_2)))
            (and (= modeA_{0} false) (= modeR_{0} true)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_3)))
            (and (= modeA_{0} false) (= modeR_{0} false)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_4)))))
""",
"""
(assert (and (>= tau_{0}_0 (/ 1 3)) (<= tau_{0}_0 0.5)
             (>= tau_{0}_t (/ 1 3)) (<= tau_{0}_t 0.5) 
             (forall_t 13 [0 time_{0}] (>= tau_{0}_t (/ 1 3)))   
             (forall_t 13 [0 time_{0}] (<= tau_{0}_t 0.5))))
(assert (or (and (= modeA_{0} true) (= modeR_{0} true)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_1)))
            (and (= modeA_{0} true) (= modeR_{0} false)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_2)))
            (and (= modeA_{0} false) (= modeR_{0} true)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_3)))
            (and (= modeA_{0} false) (= modeR_{0} false)
                 (= [xAIL_{0}_t xRDR_{0}_t tau_{0}_t r_{0}_t psi_{0}_t
                     phi_{0}_t p_{0}_t gRDR_{0}_t gAIL_{0}_t beta_{0}_t]
                    (integral 0. time_{0} 
                       [xAIL_{0}_0 xRDR_{0}_0 tau_{0}_0 r_{0}_0 psi_{0}_0 
                        phi_{0}_0 p_{0}_0 gRDR_{0}_0 gAIL_{0}_0 beta_{0}_0] flow_4)))))
"""]


# 4 steps (1/3, 1/2, 2/3, 1) * 0.5
jump_cond[0] = [
"""
(assert (and (= tau_{0}_t (/ 0.5 3))   (= tau_{1}_0 tau_{0}_t) 
             (= gRDR_{1}_0 gRDR_{0}_t) (= gAIL_{1}_0 gAIL_{0}_t) 
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t)   
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t)       
             (= beta_{1}_0 beta_{0}_t)))
(assert (= xAIL_{1}_0 xAIL_{0}_t))
(assert (= modeA_{1} modeA_{0}))
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (or (and (>= gRDR_{0}_t xRDR_{0}_t) (= modeR_{1} true))
            (and (<  gRDR_{0}_t xRDR_{0}_t) (= modeR_{1} false))))""", 
"""
(assert (and (= tau_{0}_t (/ 0.5 2))   (= tau_{1}_0 tau_{0}_t)
             (= gRDR_{1}_0 gRDR_{0}_t) (= gAIL_{1}_0 gAIL_{0}_t) 
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t)   
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t)     
             (= beta_{1}_0 beta_{0}_t)))
(assert (= xAIL_{1}_0 xAIL_{0}_t))
(assert (or (and (>= gAIL_{0}_t xAIL_{0}_t) (= modeA_{1} true))
            (and (<  gAIL_{0}_t xAIL_{0}_t) (= modeA_{1} false))))
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (= modeR_{1} modeR_{0}))""", 
"""
(assert (and (= tau_{0}_t (/ 1 3))     (= tau_{1}_0 tau_{0}_t)
             (= gRDR_{1}_0 gRDR_{0}_t) (= gAIL_{1}_0 gAIL_{0}_t) 
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t)   
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t)     
             (= beta_{1}_0 beta_{0}_t)))
(assert (= xAIL_{1}_0 xAIL_{0}_t))
(assert (= modeA_{1} modeA_{0}))
(assert (= xRDR_{1}_0 xRDR_{0}_t))
(assert (or (and (>= gRDR_{0}_t xRDR_{0}_t) (= modeR_{1} true))
            (and (<  gRDR_{0}_t xRDR_{0}_t) (= modeR_{1} false))))""", 
"""
(assert (and (= tau_{0}_t 0.5)         (= tau_{1}_0 0)
             (= gRDR_{1}_0 gRDR_{0}_t) (= gAIL_{1}_0 gAIL_{0}_t)
             (= psi_{1}_0 psi_{0}_t)   (= phi_{1}_0 phi_{0}_t) 
             (= r_{1}_0 r_{0}_t)       (= p_{1}_0 p_{0}_t) 
             (= beta_{1}_0 beta_{0}_t)))
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
             (= phi_{0}_0 0)  (= r_{0}_0 0)    (= p_{0}_0 0)    (= beta_{0}_0 0)))
(assert (and (= xAIL_{0}_0 0) (= modeA_{0} true)))
(assert (and (= xRDR_{0}_0 0) (= modeR_{0} true)))
"""

goal_cond = """
(assert (> (^ (^ beta_{0}_t 2) 0.5) 0.1))
"""

import sys
try:
    bound = int(sys.argv[1])
except:
    print("Usage:", sys.argv[0], "<Bound>")
else:
    generate(bound, 4, [0], 0, init_cond, goal_cond)

