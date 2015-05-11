
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
(define-ode flow_1 ((= d/dt[x1] (/ (- 5 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (^ x1 0.5))) 2)) 
                    (= d/dt[x2] (/ (+ 3 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x1 0.5) (^ x2 0.5)))) 4)) 
                    (= d/dt[x3] (/ (+ 4 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x2 0.5) (^ x3 0.5)))) 3))
		    (= d/dt[tau] 1)))
(define-ode flow_2 ((= d/dt[x1] (/ (- 5 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (^ x1 0.5))) 2)) 
                    (= d/dt[x2] (/ (+ 3 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x1 0.5) (^ x2 0.5)))) 4)) 
                    (= d/dt[x3] (/ (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x2 0.5) (^ x3 0.5))) 3))
		    (= d/dt[tau] 1)))
(define-ode flow_3 ((= d/dt[x1] (/ (- 5 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (^ x1 0.5))) 2)) 
                    (= d/dt[x2] (/ (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x1 0.5) (^ x2 0.5))) 4)) 
                    (= d/dt[x3] (/ (+ 4 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x2 0.5) (^ x3 0.5)))) 3))
		    (= d/dt[tau] 1)))
(define-ode flow_4 ((= d/dt[x1] (/ (- 5 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (^ x1 0.5))) 2)) 
                    (= d/dt[x2] (/ (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x1 0.5) (^ x2 0.5))) 4)) 
                    (= d/dt[x3] (/ (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x2 0.5) (^ x3 0.5))) 3))
		    (= d/dt[tau] 1)))
(define-ode flow_5 ((= d/dt[x1] (/ (* (* -0.5 (^ (* 2 9.80665) 0.5)) (^ x1 0.5)) 2)) 
                    (= d/dt[x2] (/ (+ 3 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x1 0.5) (^ x2 0.5)))) 4)) 
                    (= d/dt[x3] (/ (+ 4 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x2 0.5) (^ x3 0.5)))) 3))
		    (= d/dt[tau] 1)))
(define-ode flow_6 ((= d/dt[x1] (/ (* (* -0.5 (^ (* 2 9.80665) 0.5)) (^ x1 0.5)) 2)) 
                    (= d/dt[x2] (/ (+ 3 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x1 0.5) (^ x2 0.5)))) 4)) 
                    (= d/dt[x3] (/ (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x2 0.5) (^ x3 0.5))) 3))
		    (= d/dt[tau] 1)))
(define-ode flow_7 ((= d/dt[x1] (/ (* (* -0.5 (^ (* 2 9.80665) 0.5)) (^ x1 0.5)) 2)) 
                    (= d/dt[x2] (/ (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x1 0.5) (^ x2 0.5))) 4)) 
                    (= d/dt[x3] (/ (+ 4 (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x2 0.5) (^ x3 0.5)))) 3))
		    (= d/dt[tau] 1)))
(define-ode flow_8 ((= d/dt[x1] (/ (* (* -0.5 (^ (* 2 9.80665) 0.5)) (^ x1 0.5)) 2)) 
                    (= d/dt[x2] (/ (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x1 0.5) (^ x2 0.5))) 4)) 
                    (= d/dt[x3] (/ (* (* 0.5 (^ (* 2 9.80665) 0.5)) (- (^ x2 0.5) (^ x3 0.5))) 3))
		    (= d/dt[tau] 1)))
"""

state_dec[0] = """
(declare-fun time_{0} () Real)  
(declare-fun tau_{0}_0 () Real) 
(declare-fun tau_{0}_t () Real) 
(declare-fun mode1_{0} () Bool) 
(declare-fun x1_{0}_0 () Real)  
(declare-fun x1_{0}_t () Real)  
(declare-fun mode2_{0} () Bool)
(declare-fun x2_{0}_0 () Real)  
(declare-fun x2_{0}_t () Real)  
(declare-fun mode3_{0} () Bool)
(declare-fun x3_{0}_0 () Real)  
(declare-fun x3_{0}_t () Real)  
"""

state_val[0] = """
(assert (<= 0 time_{0}))  (assert (<= time_{0} 1))
(assert (<= 0 tau_{0}_0)) (assert (<= tau_{0}_0 1))
(assert (<= 0 tau_{0}_t)) (assert (<= tau_{0}_t 1))
(assert (<= 0 x1_{0}_0)) (assert (<= x1_{0}_0 10))
(assert (<= 0 x1_{0}_t)) (assert (<= x1_{0}_t 10))
(assert (<= 0 x2_{0}_0)) (assert (<= x2_{0}_0 10))
(assert (<= 0 x2_{0}_t)) (assert (<= x2_{0}_t 10))
(assert (<= 0 x3_{0}_0)) (assert (<= x3_{0}_0 10))
(assert (<= 0 x3_{0}_t)) (assert (<= x3_{0}_t 10))
"""

cont_cond[0] = ["""
(assert (and (>= tau_{0}_0 0) (<= tau_{0}_0 1)
             (>= tau_{0}_t 0) (<= tau_{0}_t 1)
             (forall_t 1 [0 time_{0}] (>= tau_{0}_t 0))
             (forall_t 2 [0 time_{0}] (<= tau_{0}_t 1))))
(assert (or (and (= mode1_{0} true) (= mode2_{0} true) (= mode3_{0} true)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_1)))
            (and (= mode1_{0} true) (= mode2_{0} true) (= mode3_{0} false)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_2)))
            (and (= mode1_{0} true) (= mode2_{0} false) (= mode3_{0} true)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_3)))
            (and (= mode1_{0} true) (= mode2_{0} false) (= mode3_{0} false)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_4)))
            (and (= mode1_{0} false) (= mode2_{0} true) (= mode3_{0} true)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_5)))
            (and (= mode1_{0} false) (= mode2_{0} true) (= mode3_{0} false)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_6)))
            (and (= mode1_{0} false) (= mode2_{0} false) (= mode3_{0} true)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_7)))
            (and (= mode1_{0} false) (= mode2_{0} false) (= mode3_{0} false)
                 (= [x1_{0}_t x2_{0}_t x3_{0}_t tau_{0}_t] 
                    (integral 0. time_{0} [x1_{0}_0 x2_{0}_0 x3_{0}_0 tau_{0}_0] flow_8)))))"""]

jump_cond[0] = ["""
(assert (and (= tau_{0}_t 1) (= tau_{1}_0 0)))
(assert (and (= x1_{1}_0 x1_{0}_t)))
(assert (or (and (< x1_{0}_t 5) (= mode1_{1} true))
            (and (>= x1_{0}_t 5) (= mode1_{1} false))))
(assert (and (= x2_{1}_0 x2_{0}_t)))
(assert (or (and (< x2_{0}_t 5) (= mode2_{1} true))
            (and (>= x2_{0}_t 5) (= mode2_{1} false))))
(assert (and (= x3_{1}_0 x3_{0}_t)))
(assert (or (and (< x3_{0}_t 5) (= mode3_{1} true))
            (and (>= x3_{0}_t 5) (= mode3_{1} false))))"""]


#############
# Init/Goal #
#############

init_cond = """
(assert (= tau_{0}_0 0))
(assert (= mode1_{0} true))
(assert (and (>= x1_{0}_0 (- 5 0.1)) (<= x1_{0}_0 (+ 5 0.1))))
(assert (= mode2_{0} true))
(assert (and (>= x2_{0}_0 (- 5 0.1)) (<= x2_{0}_0 (+ 5 0.1))))
(assert (= mode3_{0} true))
(assert (and (>= x3_{0}_0 (- 5 0.1)) (<= x3_{0}_0 (+ 5 0.1))))
"""

goal_cond = """
(assert (or (< x1_{0}_t (- 5 0.1)) (> x1_{0}_t (+ 5 0.1))))
(assert (or (< x2_{0}_t (- 5 0.1)) (> x2_{0}_t (+ 5 0.1))))
(assert (or (< x3_{0}_t (- 5 0.1)) (> x3_{0}_t (+ 5 0.1))))
"""

import sys
try:
    bound = int(sys.argv[1])
except:
    print("Usage:", sys.argv[0], "<Bound>")
else:
    generate(bound, 1, [0], 0, init_cond, goal_cond)

