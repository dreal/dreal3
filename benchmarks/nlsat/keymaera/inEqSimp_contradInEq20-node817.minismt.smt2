(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_contradInEq20, node 81
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun contradCoeffBiggeruscore74 () Real)
(declare-fun contradCoeffSmalleruscore76 () Real)
(declare-fun contradLeftuscore75 () Real)
(declare-fun contradRightBiggeruscore73 () Real)
(declare-fun contradRightSmalleruscore77 () Real)
(assert (not (implies (and (and (and (not (<= contradCoeffBiggeruscore74 0)) (not (<= contradCoeffSmalleruscore76 0))) (>= (+ (* (- 1) contradRightBiggeruscore73) (* contradCoeffBiggeruscore74 contradLeftuscore75)) 0)) (not (>= (+ (* (- 1) contradRightSmalleruscore77) (* contradCoeffSmalleruscore76 contradLeftuscore75)) 0))) (not (<= (+ (* contradCoeffBiggeruscore74 contradRightSmalleruscore77) (* (- 1) (* contradCoeffSmalleruscore76 contradRightBiggeruscore73))) 0)))))
(check-sat)
