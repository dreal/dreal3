(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl42, node 64
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const d Real)
(declare-const c Real)
(declare-const a Real)
(declare-const b Real)
(assert (not (=> (and (and (< 0. (* d c) ) (< 0. (* c a) )) (< 0. (* b a) )) (< 0. (* d b) ))))
(check-sat)
(exit)
