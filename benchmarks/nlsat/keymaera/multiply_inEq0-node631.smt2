(set-logic QF_NRA)
(set-info :source | KeYmaera example: multiply_inEq0, node 63
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const multFacuscore103 Real)
(declare-const multLeftuscore105 Real)
(declare-const multRightuscore104 Real)
(assert (not (=> (and (>= multFacuscore103 0. ) (<= multLeftuscore105 multRightuscore104 )) (<= (* multLeftuscore105 multFacuscore103) (* multRightuscore104 multFacuscore103) ))))
(check-sat)
(exit)
