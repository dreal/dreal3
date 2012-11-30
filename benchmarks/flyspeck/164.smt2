(set-logic QF_NLR)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= 4.0 x1) (<= x1 6.3504))(and (<= 4.0 x2) (<= x2 6.3504))(and (<= 4.0 x3) (<= x3 6.3504))(and (<= 4.0 x4) (<= x4 6.3504))(and (<= 4.0 x5) (<= x5 6.3504))(and (<= 8.0 x6) (<= x6 25.4016))(not (> (+ (- (* (- x2) x3) (* x1 x4)) (+ (* x2 x5) (+ (- (* x3 x6) (* x5 x6)) (* x1 (+ (- x1) (+ x2 (+ (- x3 x4) (+ x5 x6)))))))) 0.0)))
)
(check-sat)
(exit)
