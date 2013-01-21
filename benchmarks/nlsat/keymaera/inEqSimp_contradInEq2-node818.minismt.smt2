(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_contradInEq2, node 81
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun contradCoeffBiggeruscore65 () Real)
(declare-fun contradCoeffSmalleruscore67 () Real)
(declare-fun contradLeftuscore66 () Real)
(declare-fun contradRightBiggeruscore64 () Real)
(declare-fun contradRightSmalleruscore68 () Real)
(assert (not (implies (and (and (and (not (<= contradCoeffBiggeruscore65 0)) (not (<= contradCoeffSmalleruscore67 0))) (>= (+ (* (- 1) contradRightBiggeruscore64) (* contradCoeffBiggeruscore65 contradLeftuscore66)) 0)) (<= (+ (* (- 1) contradRightSmalleruscore68) (* contradCoeffSmalleruscore67 contradLeftuscore66)) 0)) (>= (+ (* contradCoeffBiggeruscore65 contradRightSmalleruscore68) (* (- 1) (* contradCoeffSmalleruscore67 contradRightBiggeruscore64))) 0))))
(check-sat)
