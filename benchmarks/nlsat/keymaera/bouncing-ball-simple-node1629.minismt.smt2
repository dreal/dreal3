(set-logic QF_NRA)
(set-info :source | KeYmaera example: bouncing-ball-simple, node 162
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun h () Real)
(declare-fun v () Real)
(assert (not (implies (and (= h 0) (= v 16)) (<= v 16))))
(check-sat)
