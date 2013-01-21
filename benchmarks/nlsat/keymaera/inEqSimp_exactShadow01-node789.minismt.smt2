(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_exactShadow01, node 78
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun esCoeff1uscore40 () Real)
(declare-fun esCoeff2uscore38 () Real)
(declare-fun esLeftuscore41 () Real)
(declare-fun esRight1uscore37 () Real)
(declare-fun esRight2uscore39 () Real)
(assert (not (implies (and (and (and (not (<= esCoeff1uscore40 0)) (not (<= esCoeff2uscore38 0))) (not (>= (+ (* (- 1) esRight1uscore37) (* esCoeff1uscore40 esLeftuscore41)) 0))) (>= (+ (* (- 1) esRight2uscore39) (* esCoeff2uscore38 esLeftuscore41)) 0)) (not (<= (+ (* (- 1) (* esCoeff1uscore40 esRight2uscore39)) (* esCoeff2uscore38 esRight1uscore37)) 0)))))
(check-sat)
