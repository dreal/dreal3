(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert (<= 2.6181 x1))
(assert (<= x1 2.6508))
(assert (<= 2.0 x2))
(assert (<= x2 2.46350884418))
(assert (<= 2.0 x3))
(assert (<= x3 2.46350884418))
(assert (<= 2.0 x4))
(assert (<= x4 2.46350884418))
(assert (<= 2.0 x5))
(assert (<= x5 2.46350884418))
(assert (<= 1.0 x6))
(assert (<= x6 1.0))
(assert (not (< (+ (* 1.0 (* 2.0 (* 3.14159265 0.126777))) (+ (* x1 (- 0.053069)) (+ (* x1 0.196466) (+ (* x1 (- 0.093532)) (+ (* x1 (- 0.049865)) (+ (* x2 (* 2.0 0.003525)) (+ (* x2 (* 2.0 (- 0.003525))) (+ (* x3 (* 2.0 (- 0.003525))) (+ (* x3 (* 2.0 0.003525)) (+ (* x4 (* 2.0 0.003525)) (+ (* x4 (* 2.0 (- 0.003525))) (+ (* x5 (* 2.0 (- 0.003525))) (+ (* x5 (* 2.0 0.003525)) (+ (* 1.0 (- 0.142652)) (+ (* 1.0 (- 0.667227)) (+ (* 1.0 0.035622) (* 1.0 (- 0.022307)))))))))))))))))) 0.0)))
(check-sat)
(exit)
