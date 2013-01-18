(set-logic QF_NRA)
(set-info :source | KeYmaera example: multiply_inEq2, node 65
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const multFacuscore112 Real)
(declare-const multLeftuscore111 Real)
(declare-const multRightuscore110 Real)
(assert (not (=> (and (> multFacuscore112 0. ) (< multLeftuscore111 multRightuscore110 )) (< (* multLeftuscore111 multFacuscore112) (* multRightuscore110 multFacuscore112) ))))
(check-sat)
