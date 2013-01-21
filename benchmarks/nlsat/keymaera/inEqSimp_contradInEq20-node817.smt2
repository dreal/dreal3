(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_contradInEq20, node 81
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const contradCoeffBiggeruscore74 Real)
(declare-const contradCoeffSmalleruscore76 Real)
(declare-const contradLeftuscore75 Real)
(declare-const contradRightBiggeruscore73 Real)
(declare-const contradRightSmalleruscore77 Real)
(assert (not (=> (and (and (and (> contradCoeffBiggeruscore74 0. ) (> contradCoeffSmalleruscore76 0. )) (>= (* contradLeftuscore75 contradCoeffBiggeruscore74) contradRightBiggeruscore73 )) (< (* contradLeftuscore75 contradCoeffSmalleruscore76) contradRightSmalleruscore77 )) (> (* contradCoeffBiggeruscore74 contradRightSmalleruscore77) (* contradCoeffSmalleruscore76 contradRightBiggeruscore73) ))))
(check-sat)
(exit)
