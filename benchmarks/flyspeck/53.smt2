(set-logic QF_NRA)
(declare-fun e1 () Real)
(declare-fun e2 () Real)
(declare-fun e3 () Real)
(declare-fun a2 () Real)
(declare-fun b2 () Real)
(declare-fun c2 () Real)
(assert
(and
(and (<= 1 e1) (<= e1 (/ 117547965743 100000000000)))(and (<= 1 e2) (<= e2 (/ 117547965743 100000000000)))(and (<= 1 e3) (<= e3 (/ 117547965743 100000000000)))(and (<= (/ 56644 10000) a2) (<= a2 (/ 90601 10000)))(and (<= 4 b2) (<= b2 (/ 63504 10000)))(and (<= (/ 625 100) c2) (<= c2 (/ 1553 100)))(not (> (* (- 4) (+ (* (^ a2 2) e1) (- (* 8 (* (- b2 c2) (- e2 e3))) (* a2 (+ (* 16 e1) (+ (* (- b2 8) e2) (* (- c2 8) e3))))))) 0)))
)
(check-sat)
(exit)
