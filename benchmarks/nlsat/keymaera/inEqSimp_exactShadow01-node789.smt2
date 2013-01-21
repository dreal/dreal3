(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_exactShadow01, node 78
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const esCoeff1uscore40 Real)
(declare-const esCoeff2uscore38 Real)
(declare-const esLeftuscore41 Real)
(declare-const esRight1uscore37 Real)
(declare-const esRight2uscore39 Real)
(assert (not (=> (and (and (and (> esCoeff1uscore40 0. ) (> esCoeff2uscore38 0. )) (< (* esLeftuscore41 esCoeff1uscore40) esRight1uscore37 )) (>= (* esLeftuscore41 esCoeff2uscore38) esRight2uscore39 )) (> (+ (* (- 1.) (* esCoeff1uscore40 esRight2uscore39)) (* esCoeff2uscore38 esRight1uscore37)) 0. ))))
(check-sat)
(exit)
