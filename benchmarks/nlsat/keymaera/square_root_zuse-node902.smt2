(set-logic QF_NRA)
(set-info :source | KeYmaera example: square_root_zuse, node 90
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const a Real)
(assert (not (= a (+ 1. (* 1. (- a 1.))) )))
(check-sat)
(exit)
