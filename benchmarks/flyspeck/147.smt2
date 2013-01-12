(set-logic QF_NRA)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(declare-fun y4 () Real)
(declare-fun y5 () Real)
(declare-fun y6 () Real)
(assert
(and
(and (<= 3 y1) (<= y1 3))(and (<= 2 y2) (<= y2 (/ 252 100)))(and (<= 2 y3) (<= y3 (/ 252 100)))(and (<= 3 y4) (<= y4 3))(and (<= 2 y5) (<= y5 (/ 252 100)))(and (<= 2 y6) (<= y6 (/ 252 100)))(not (or (< (+ (* (* y1 y1) (* (* y4 y4) (+ (- (* y1 y1)) (+ (* y2 y2) (+ (- (* y3 y3) (* y4 y4)) (+ (* y5 y5) (* y6 y6))))))) (+ (* (* y2 y2) (* (* y5 y5) (+ (- (* y1 y1) (* y2 y2)) (+ (* y3 y3) (+ (- (* y4 y4) (* y5 y5)) (* y6 y6)))))) (- (- (- (- (* (* y3 y3) (* (* y6 y6) (+ (* y1 y1) (+ (- (* y2 y2) (* y3 y3)) (+ (* y4 y4) (- (* y5 y5) (* y6 y6))))))) (* (* y2 y2) (* (* y3 y3) (* y4 y4)))) (* (* y1 y1) (* (* y3 y3) (* y5 y5)))) (* (* y1 y1) (* (* y2 y2) (* y6 y6)))) (* (* y4 y4) (* (* y5 y5) (* y6 y6)))))) 0) (or (> (+ y2 (+ y3 (+ y5 y6))) (/ 8472 1000)) (or (< y2 y3) (or (< y2 y5) (or (< y2 y6) (< y3 y6))))))))
)
(check-sat)
(exit)
