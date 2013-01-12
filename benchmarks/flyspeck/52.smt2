(set-logic QF_NRA)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(declare-fun y4 () Real)
(declare-fun y5 () Real)
(declare-fun y6 () Real)
(assert
(and
(and (<= 2 y1) (<= y1 (/ 252 100)))(and (<= 2 y2) (<= y2 (/ 252 100)))(and (<= 2 y3) (<= y3 2))(and (<= (/ 301 100) y4) (<= y4 (/ 301 100)))(and (<= 2 y5) (<= y5 (/ 252 100)))(and (<= 2 y6) (<= y6 2))(not (< (+ (- (* (- (* y2 y2)) (* y3 y3)) (* (* y1 y1) (* y4 y4))) (+ (* (* y2 y2) (* y5 y5)) (+ (- (* (* y3 y3) (* y6 y6)) (* (* y5 y5) (* y6 y6))) (* (* y1 y1) (+ (- (* y1 y1)) (+ (* y2 y2) (+ (- (* y3 y3) (* y4 y4)) (+ (* y5 y5) (* y6 y6))))))))) 0)))
)
(check-sat)
(exit)
