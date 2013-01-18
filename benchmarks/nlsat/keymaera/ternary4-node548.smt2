(set-logic QF_NRA)
(set-info :source | KeYmaera example: ternary4, node 54
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const x Real)
(declare-const z Real)
(declare-const y Real)
(assert (not (>= (+ (+ (- (+ (- (+ (- (+ (+ (* x x x x) (* (* 2. (* x x)) z)) (* x x)) (* (* (* 2. x) y) z)) (* (* 2. (* y y)) (* z z))) (* (* 2. y) (* z z))) (* 2. (* z z))) (* 2. x)) (* (* 2. y) z)) 1.) 0. )))
(check-sat)
