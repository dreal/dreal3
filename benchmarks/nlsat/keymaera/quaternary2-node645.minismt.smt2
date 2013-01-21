(set-logic QF_NRA)
(set-info :source | KeYmaera example: quaternary2, node 64
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun w () Real)
(assert (not (>= (+ (* 2 (* z z)) (* 3 (* w w)) (* 2 (* x y)) (* 2 (* x x w)) (* 2 (* y y w)) (* x x x x) (* y y y y) (* z z z z) (* w w w w) (* 4 (* x x y y)) (* 2 (* x y z z)) (* 2 (* x y w w)) (* 2 (* z z w w))) (- 1))))
(check-sat)
