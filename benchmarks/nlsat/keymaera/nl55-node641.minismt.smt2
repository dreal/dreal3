(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl55, node 64
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun x5 () Real)
(declare-fun x4 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x1 () Real)
(assert (not (implies (and (and (<= (+ x5 (* (- 1) x4)) 0) (= (+ (* (- 1) x5) x2 (* (- 1) x3)) 0)) (<= (+ (* (- 1) x5) x4) 0)) (= (+ (* x2 x1) (* (- 1) (* x4 x1)) (* (- 1) (* x3 x1))) 0))))
(check-sat)
