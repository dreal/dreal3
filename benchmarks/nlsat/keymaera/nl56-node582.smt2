(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl56, node 58
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const a Real)
(declare-const b Real)
(declare-const x Real)
(assert (not (=> (and (<= a (+ b x) ) (< 2. x )) (< a (+ b (* x x)) ))))
(check-sat)
(exit)
