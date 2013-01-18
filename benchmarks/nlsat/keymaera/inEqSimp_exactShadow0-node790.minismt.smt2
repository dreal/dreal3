(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_exactShadow0, node 79
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun esCoeff1uscore31 () Real)
(declare-fun esCoeff2uscore29 () Real)
(declare-fun esLeftuscore32 () Real)
(declare-fun esRight1uscore28 () Real)
(declare-fun esRight2uscore30 () Real)
(assert (not (implies (and (and (and (not (<= esCoeff1uscore31 0)) (not (<= esCoeff2uscore29 0))) (<= (+ (* (- 1) esRight1uscore28) (* esCoeff1uscore31 esLeftuscore32)) 0)) (>= (+ (* (- 1) esRight2uscore30) (* esCoeff2uscore29 esLeftuscore32)) 0)) (>= (+ (* (- 1) (* esCoeff1uscore31 esRight2uscore30)) (* esCoeff2uscore29 esRight1uscore28)) 0))))
(check-sat)
