(set-logic QF_NLR)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= 3.0 x1) (<= x1 64.0))(and (<= 1.0 x2) (<= x2 1.0))(and (<= 1.0 x3) (<= x3 1.0))(and (<= 1.0 x4) (<= x4 1.0))(and (<= 1.0 x5) (<= x5 1.0))(and (<= 1.0 x6) (<= x6 1.0))(not (> (- (* 2.0 3.14159265) (* 2.0 (* x1 (arcsin (* (cos 0.797) (sin (/ 3.14159265 x1))))))) (+ (- 0.591 (* 0.0331 x1)) (+ (* 0.506 (/ (- 1.26 1.0) (- 1.26 1.0))) 1.0)))))
)
(check-sat)
(exit)
