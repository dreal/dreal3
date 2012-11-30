(set-logic QF_NLR)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= 7.84 x1) (<= x1 8.0))(and (<= 4.0 x2) (<= x2 4.0401))(and (<= 4.0 x3) (<= x3 4.0401))(and (<= 7.84 x4) (<= x4 8.0))(and (<= 4.0 x5) (<= x5 4.0401))(and (<= 4.0 x6) (<= x6 4.0401))(not (< 0.0 (+ (* (^ x1 0.5) (* (^ x2 0.5) (^ x3 0.5))) (+ (* (^ x1 0.5) (/ (+ x2 (- x3 x4)) 2.0)) (+ (* (^ x2 0.5) (/ (+ x1 (- x3 x5)) 2.0)) (* (^ x3 0.5) (/ (+ x1 (- x2 x6)) 2.0))))))))
)
(check-sat)
(exit)
