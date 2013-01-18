(set-logic QF_NRA)
(set-info :source | KeYmaera example: quaternary4, node 62
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const w Real)
(declare-const z Real)
(declare-const x Real)
(declare-const y Real)
(assert (not (>= (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* w w w w w w) (* (* 2. (* z z)) (* w w w))) (* x x x x)) (* y y y y)) (* z z z z)) (* (* 2. (* x x)) w)) (* (* 2. (* x x)) z)) (* 3. (* x x))) (* w w)) (* (* 2. z) w)) (* z z)) (* 2. z)) (* 2. w)) 1.) 0. )))
(check-sat)
