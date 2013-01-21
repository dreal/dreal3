(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_subsumption20, node 82
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const subsumCoeffSmalleruscore58 Real)
(declare-const subsumCoeffBiggeruscore56 Real)
(declare-const subsumRightSmalleruscore59 Real)
(declare-const subsumRightBiggeruscore55 Real)
(declare-const subsumLeftuscore57 Real)
(assert (not (=> (and (and (and (> subsumCoeffSmalleruscore58 0. ) (> subsumCoeffBiggeruscore56 0. )) (<= (* subsumCoeffBiggeruscore56 subsumRightSmalleruscore59) (* subsumCoeffSmalleruscore58 subsumRightBiggeruscore55) )) (< (* subsumLeftuscore57 subsumCoeffSmalleruscore58) subsumRightSmalleruscore59 )) (<= (* subsumLeftuscore57 subsumCoeffBiggeruscore56) subsumRightBiggeruscore55 ))))
(check-sat)
(exit)
