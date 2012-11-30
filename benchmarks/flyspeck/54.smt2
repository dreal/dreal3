(set-logic QF_NLR)
(declare-fun e1 () Real)
(declare-fun e2 () Real)
(declare-fun e3 () Real)
(declare-fun a2 () Real)
(declare-fun b2 () Real)
(declare-fun c2 () Real)
(assert
(and
(and (<= 1.0 e1) (<= e1 1.17547965743))(and (<= 1.0 e2) (<= e2 1.17547965743))(and (<= 1.0 e3) (<= e3 1.17547965743))(and (<= 2.51952632905 a2) (<= a2 9.0601))(and (<= 5.6644 b2) (<= b2 15.53))(and (<= 5.6644 c2) (<= c2 15.53))(not (> (* (- 4.0) (+ (* (^ a2 2.0) e1) (- (* 8.0 (* (- b2 c2) (- e2 e3))) (* a2 (+ (* 16.0 e1) (+ (* (- b2 8.0) e2) (* (- c2 8.0) e3))))))) 0.0)))
)
(check-sat)
(exit)
