(set-logic QF_NRA)
(set-info :source | KeYmaera example: ternary5, node 67
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (not (>= (+ (* y y z z) (* 2 (* x x y y y z)) (* (- 2) (* x y z z z z)) (* x x x x y y y y) (* (- 4) (* x x x y y z z z)) (* x x z z z z z z) (* (- 2) (* x x x x x y y y z z)) (* 2 (* x x x x y z z z z z)) (* x x x x x x y y z z z z)) 0)))
(check-sat)
