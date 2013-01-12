(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= 4 x1) (<= x1 (/ 40401 10000)))(and (<= 4 x2) (<= x2 (/ 40401 10000)))(and (<= (/ 784 100) x3) (<= x3 8))(and (<= 4 x4) (<= x4 (/ 40401 10000)))(and (<= 4 x5) (<= x5 (/ 40401 10000)))(and (<= (/ 784 100) x6) (<= x6 8))(not (< 0 (+ (- (* (- x2) x3) (* x1 x4)) (+ (* x2 x5) (+ (- (* x3 x6) (* x5 x6)) (* x1 (+ (- x1) (+ x2 (+ (- x3 x4) (+ x5 x6)))))))))))
)
(check-sat)
(exit)
