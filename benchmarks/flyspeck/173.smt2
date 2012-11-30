(set-logic QF_NLR)
(declare-fun h () Real)
(assert
(and
(and (<= 1.0 h) (<= h 1.0))(not (< (+ (- 0.591 (* 0.0331 64.0)) (+ (* 0.506 (/ (- 1.26 1.0) (- 1.26 1.0))) 1.0)) 0.0)))
)
(check-sat)
(exit)
