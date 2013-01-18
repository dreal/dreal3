(set-logic QF_NRA)
(set-info :source | KeYmaera example: quaternary4, node 62
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun w () Real)
(declare-fun z () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (>= (+ (* 2 w) (* 2 z) (* z z) (* 3 (* x x)) (* w w) (* 2 (* w z)) (* 2 (* w x x)) (* 2 (* z x x)) (* x x x x) (* y y y y) (* z z z z) (* 2 (* w w w z z)) (* w w w w w w)) (- 1))))
(check-sat)
