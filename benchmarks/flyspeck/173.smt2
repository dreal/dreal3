(set-logic QF_NRA)
(declare-fun h () Real)
(assert
(and
(and (<= 1 h) (<= h 1))(not (< (+ (- (/ 591 1000) (* (/ 0331 10000) 64)) (+ (* (/ 506 1000) (/ (- (/ 126 100) 1) (- (/ 126 100) 1))) 1)) 0)))
)
(check-sat)
(exit)
