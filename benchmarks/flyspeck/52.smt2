(set-logic QF_NLR)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(declare-fun y4 () Real)
(declare-fun y5 () Real)
(declare-fun y6 () Real)
(assert
(and
(and (<= 2.0 y1) (<= y1 2.52))(and (<= 2.0 y2) (<= y2 2.52))(and (<= 2.0 y3) (<= y3 2.0))(and (<= 3.01 y4) (<= y4 3.01))(and (<= 2.0 y5) (<= y5 2.52))(and (<= 2.0 y6) (<= y6 2.0))(not (< (+ (- (* (- (* y2 y2)) (* y3 y3)) (* (* y1 y1) (* y4 y4))) (+ (* (* y2 y2) (* y5 y5)) (+ (- (* (* y3 y3) (* y6 y6)) (* (* y5 y5) (* y6 y6))) (* (* y1 y1) (+ (- (* y1 y1)) (+ (* y2 y2) (+ (- (* y3 y3) (* y4 y4)) (+ (* y5 y5) (* y6 y6))))))))) 0.0)))
)
(check-sat)
(exit)
