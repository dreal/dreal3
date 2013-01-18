(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl3, node 73
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun x2 () Real)
(declare-fun x1 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(assert (and (and (and (not (<= x2 3)) (= (* x2 x2 x1) 0)) (not (>= (* 2 (* x2 x1 x1 x1 x3 x3 x4 x4 x4 x4 x4 x4)) 0))) (not (<= x1 2))))
(check-sat)
