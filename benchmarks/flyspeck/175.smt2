(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= 1 x1) (<= x1 (/ 126 100)))(and (<= 3 x2) (<= x2 34))(and (<= 1 x3) (<= x3 1))(and (<= 1 x4) (<= x4 1))(and (<= 1 x5) (<= x5 1))(and (<= 1 x6) (<= x6 1))(not (> (- (* 2 (/ 314159265 100000000)) (* 2 (* x2 (arcsin (* (+ (* x1 (/ (^ 3 (/ 5 10)) 4)) (/ (^ (- 1 (^ (/ x1 2) 2)) (/ 5 10)) 2)) (sin (/ (/ 314159265 100000000) x2))))))) (+ (- (/ 591 1000) (* (/ 0331 10000) x2)) (* (/ 506 1000) (/ (- (/ 126 100) x1) (- (/ 126 100) 1)))))))
)
(check-sat)
(exit)
