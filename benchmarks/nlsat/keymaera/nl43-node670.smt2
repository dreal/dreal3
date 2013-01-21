(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl43, node 67
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const y Real)
(declare-const z Real)
(declare-const x Real)
(assert (not (=> (and (and (>= y 1. ) (= (* (* z z) 2.) y )) (>= x 1. )) (<= (* (* z z) x) (* y x) ))))
(check-sat)
(exit)
