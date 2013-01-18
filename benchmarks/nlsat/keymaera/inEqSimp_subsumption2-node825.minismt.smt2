(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_subsumption2, node 82
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun subsumCoeffSmalleruscore49 () Real)
(declare-fun subsumCoeffBiggeruscore47 () Real)
(declare-fun subsumRightSmalleruscore50 () Real)
(declare-fun subsumRightBiggeruscore46 () Real)
(declare-fun subsumLeftuscore48 () Real)
(assert (not (implies (and (and (and (not (<= subsumCoeffSmalleruscore49 0)) (not (<= subsumCoeffBiggeruscore47 0))) (<= (+ (* subsumCoeffBiggeruscore47 subsumRightSmalleruscore50) (* (- 1) (* subsumCoeffSmalleruscore49 subsumRightBiggeruscore46))) 0)) (<= (+ (* (- 1) subsumRightSmalleruscore50) (* subsumCoeffSmalleruscore49 subsumLeftuscore48)) 0)) (<= (+ (* (- 1) subsumRightBiggeruscore46) (* subsumCoeffBiggeruscore47 subsumLeftuscore48)) 0))))
(check-sat)
