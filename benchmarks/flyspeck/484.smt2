(set-logic QF_NLR)
(declare-fun dummy () Real)
(assert
(and
(and (<= 1.0 dummy) (<= dummy 1.0))(not (> (+ (* 5.0 0.0560305) (* (- 0.0445813) (* 2.0 3.14159265))) 0.0)))
)
(check-sat)
(exit)
