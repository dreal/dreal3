(set-logic QF_NLR)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(declare-fun y4 () Real)
(declare-fun y5 () Real)
(declare-fun y6 () Real)
(assert
(and
(and (<= 2.82842712475 y1) (<= y1 3.0))(and (<= 2.0 y2) (<= y2 2.07))(and (<= 2.0 y3) (<= y3 2.07))(and (<= 2.82842712475 y4) (<= y4 5.04))(and (<= 2.0 y5) (<= y5 2.07))(and (<= 2.0 y6) (<= y6 2.07))(not (> (+ y2 (+ y3 (+ y5 (- (- y6 7.99) (* 0.00385 (+ (* (* y1 y1) (* (* y4 y4) (+ (- (* y1 y1)) (+ (* y2 y2) (+ (- (* y3 y3) (* y4 y4)) (+ (* y5 y5) (* y6 y6))))))) (+ (* (* y2 y2) (* (* y5 y5) (+ (- (* y1 y1) (* y2 y2)) (+ (* y3 y3) (+ (- (* y4 y4) (* y5 y5)) (* y6 y6)))))) (- (- (- (- (* (* y3 y3) (* (* y6 y6) (+ (* y1 y1) (+ (- (* y2 y2) (* y3 y3)) (+ (* y4 y4) (- (* y5 y5) (* y6 y6))))))) (* (* y2 y2) (* (* y3 y3) (* y4 y4)))) (* (* y1 y1) (* (* y3 y3) (* y5 y5)))) (* (* y1 y1) (* (* y2 y2) (* y6 y6)))) (* (* y4 y4) (* (* y5 y5) (* y6 y6))))))))))) (* 2.75 (- (/ (+ y1 y4) 2.0) (^ 8.0 0.5))))))
)
(check-sat)
(exit)
