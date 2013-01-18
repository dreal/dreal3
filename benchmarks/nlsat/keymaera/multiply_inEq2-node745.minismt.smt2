(set-logic QF_NRA)
(set-info :source | KeYmaera example: multiply_inEq2, node 74
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun multFacuscore112 () Real)
(declare-fun multLeftuscore111 () Real)
(declare-fun multRightuscore110 () Real)
(assert (not (implies (and (not (>= multFacuscore112 0)) (not (>= (+ multLeftuscore111 (* (- 1) multRightuscore110)) 0))) (or (not (<= multFacuscore112 0)) (not (<= (+ (* multFacuscore112 multLeftuscore111) (* (- 1) (* multFacuscore112 multRightuscore110))) 0))))))
(check-sat)
