(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl43, node 67
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun x () Real)
(assert (not (implies (and (and (>= y 1) (= (+ (* (- 1) y) (* 2 (* z z))) 0)) (>= x 1)) (<= (+ (* (- 1) (* y x)) (* z z x)) 0))))
(check-sat)
