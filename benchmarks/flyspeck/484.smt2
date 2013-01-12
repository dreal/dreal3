(set-logic QF_NRA)
(declare-fun dummy () Real)
(assert
(and
(and (<= 1 dummy) (<= dummy 1))(not (> (+ (* 5 (/ 0560305 10000000)) (* (- (/ 0445813 10000000)) (* 2 (/ 314159265 100000000)))) 0)))
)
(check-sat)
(exit)
