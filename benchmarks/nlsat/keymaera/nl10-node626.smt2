(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl10, node 62
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert (not (not (and (and (and (= x1 1. ) (>= x2 2. )) (>= x3 4. )) (<= (+ x3 (* x2 x1)) 5. )))))
(check-sat)
(exit)
