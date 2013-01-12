(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= (/ 784 100) x1) (<= x1 8))(and (<= 4 x2) (<= x2 (/ 40401 10000)))(and (<= 4 x3) (<= x3 (/ 40401 10000)))(and (<= (/ 784 100) x4) (<= x4 8))(and (<= 4 x5) (<= x5 (/ 40401 10000)))(and (<= 4 x6) (<= x6 (/ 40401 10000)))(not (< 0 (+ (* (^ x1 (/ 5 10)) (* (^ x2 (/ 5 10)) (^ x3 (/ 5 10)))) (+ (* (^ x1 (/ 5 10)) (/ (+ x2 (- x3 x4)) 2)) (+ (* (^ x2 (/ 5 10)) (/ (+ x1 (- x3 x5)) 2)) (* (^ x3 (/ 5 10)) (/ (+ x1 (- x2 x6)) 2))))))))
)
(check-sat)
(exit)
