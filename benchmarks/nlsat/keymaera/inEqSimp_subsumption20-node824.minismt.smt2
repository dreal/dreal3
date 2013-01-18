(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_subsumption20, node 82
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun subsumCoeffSmalleruscore58 () Real)
(declare-fun subsumCoeffBiggeruscore56 () Real)
(declare-fun subsumRightSmalleruscore59 () Real)
(declare-fun subsumRightBiggeruscore55 () Real)
(declare-fun subsumLeftuscore57 () Real)
(assert (not (implies (and (and (and (not (<= subsumCoeffSmalleruscore58 0)) (not (<= subsumCoeffBiggeruscore56 0))) (<= (+ (* subsumCoeffBiggeruscore56 subsumRightSmalleruscore59) (* (- 1) (* subsumCoeffSmalleruscore58 subsumRightBiggeruscore55))) 0)) (not (>= (+ (* (- 1) subsumRightSmalleruscore59) (* subsumCoeffSmalleruscore58 subsumLeftuscore57)) 0))) (<= (+ (* (- 1) subsumRightBiggeruscore55) (* subsumCoeffBiggeruscore56 subsumLeftuscore57)) 0))))
(check-sat)
