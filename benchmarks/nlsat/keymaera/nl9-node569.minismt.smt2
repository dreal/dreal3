(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl9, node 56
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun x2 () Real)
(declare-fun x1 () Real)
(assert (and (and (not (<= (* x2 x1) 0)) (not (>= x1 0))) (not (<= x1 0))))
(check-sat)
