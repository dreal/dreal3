(set-logic QF_NLR)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(declare-fun y4 () Real)
(declare-fun y5 () Real)
(declare-fun y6 () Real)
(assert
(and
(and (<= 2.82842712475 y1) (<= y1 3.0))(and (<= 2.07 y2) (<= y2 2.52))(and (<= 2.0 y3) (<= y3 2.52))(and (<= 3.0 y4) (<= y4 3.0))(and (<= 2.0 y5) (<= y5 2.52))(and (<= 2.0 y6) (<= y6 2.52))(not (or (> (+ y2 (+ y3 (+ y5 (- y6 7.99)))) (* 2.75 (- y1 (^ 8.0 0.5)))))))
)
(check-sat)
(exit)
