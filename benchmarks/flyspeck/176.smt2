(set-logic QF_NLR)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= 1.0 x1) (<= x1 1.26))(and (<= 1.0 x2) (<= x2 1.0))(and (<= 1.0 x3) (<= x3 1.0))(and (<= 1.0 x4) (<= x4 1.0))(and (<= 1.0 x5) (<= x5 1.0))(and (<= 1.0 x6) (<= x6 1.0))(not (< (+ (- 0.591 (* 0.0331 34.0)) (* 0.506 (/ (- 1.26 x1) (- 1.26 1.0)))) 0.0)))
)
(check-sat)
(exit)
