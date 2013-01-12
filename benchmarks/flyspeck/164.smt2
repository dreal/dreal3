(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert
(and
(and (<= 4 x1) (<= x1 (/ 63504 10000)))(and (<= 4 x2) (<= x2 (/ 63504 10000)))(and (<= 4 x3) (<= x3 (/ 63504 10000)))(and (<= 4 x4) (<= x4 (/ 63504 10000)))(and (<= 4 x5) (<= x5 (/ 63504 10000)))(and (<= 8 x6) (<= x6 (/ 254016 10000)))(not (> (+ (- (* (- x2) x3) (* x1 x4)) (+ (* x2 x5) (+ (- (* x3 x6) (* x5 x6)) (* x1 (+ (- x1) (+ x2 (+ (- x3 x4) (+ x5 x6)))))))) 0)))
)
(check-sat)
(exit)
