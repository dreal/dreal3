(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= 3 x1) (<= x1 64))(and (<= 1 x2) (<= x2 1))(and (<= 1 x3) (<= x3 1))(and (<= 1 x4) (<= x4 1))(and (<= 1 x5) (<= x5 1))(and (<= 1 x6) (<= x6 1))(not (> (- (* 2 (/ 314159265 100000000)) (* 2 (* x1 (arcsin (* (cos (/ 797 1000)) (sin (/ (/ 314159265 100000000) x1))))))) (+ (- (/ 591 1000) (* (/ 0331 10000) x1)) (+ (* (/ 506 1000) (/ (- (/ 126 100) 1) (- (/ 126 100) 1))) 1)))))
)
(check-sat)
(exit)
