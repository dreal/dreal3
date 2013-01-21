(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_subsumption2, node 82
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const subsumCoeffSmalleruscore49 Real)
(declare-const subsumCoeffBiggeruscore47 Real)
(declare-const subsumRightSmalleruscore50 Real)
(declare-const subsumRightBiggeruscore46 Real)
(declare-const subsumLeftuscore48 Real)
(assert (not (=> (and (and (and (> subsumCoeffSmalleruscore49 0. ) (> subsumCoeffBiggeruscore47 0. )) (<= (* subsumCoeffBiggeruscore47 subsumRightSmalleruscore50) (* subsumCoeffSmalleruscore49 subsumRightBiggeruscore46) )) (<= (* subsumLeftuscore48 subsumCoeffSmalleruscore49) subsumRightSmalleruscore50 )) (<= (* subsumLeftuscore48 subsumCoeffBiggeruscore47) subsumRightBiggeruscore46 ))))
(check-sat)
(exit)
