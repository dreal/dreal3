(set-logic QF_NRA)
(set-info :source | KeYmaera example: decompose_mult, node 50
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun iuscore5 () Real)
(declare-fun i0uscore4 () Real)
(assert (not (implies (= (* iuscore5 i0uscore4) 0) (or (= iuscore5 0) (= i0uscore4 0)))))
(check-sat)
