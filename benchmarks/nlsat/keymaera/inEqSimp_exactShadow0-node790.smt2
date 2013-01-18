(set-logic QF_NRA)
(set-info :source | KeYmaera example: inEqSimp_exactShadow0, node 79
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const esCoeff1uscore31 Real)
(declare-const esCoeff2uscore29 Real)
(declare-const esLeftuscore32 Real)
(declare-const esRight1uscore28 Real)
(declare-const esRight2uscore30 Real)
(assert (not (=> (and (and (and (> esCoeff1uscore31 0. ) (> esCoeff2uscore29 0. )) (<= (* esLeftuscore32 esCoeff1uscore31) esRight1uscore28 )) (>= (* esLeftuscore32 esCoeff2uscore29) esRight2uscore30 )) (>= (+ (* (- 1.) (* esCoeff1uscore31 esRight2uscore30)) (* esCoeff2uscore29 esRight1uscore28)) 0. ))))
(check-sat)
