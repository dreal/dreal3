(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_contradInEq2, node 81
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const contradCoeffBiggeruscore65 Real)
(declare-const contradCoeffSmalleruscore67 Real)
(declare-const contradLeftuscore66 Real)
(declare-const contradRightBiggeruscore64 Real)
(declare-const contradRightSmalleruscore68 Real)
(assert (not (=> (and (and (and (> contradCoeffBiggeruscore65 0. ) (> contradCoeffSmalleruscore67 0. )) (>= (* contradLeftuscore66 contradCoeffBiggeruscore65) contradRightBiggeruscore64 )) (<= (* contradLeftuscore66 contradCoeffSmalleruscore67) contradRightSmalleruscore68 )) (>= (* contradCoeffBiggeruscore65 contradRightSmalleruscore68) (* contradCoeffSmalleruscore67 contradRightBiggeruscore64) ))))
(check-sat)
(exit)
