(set-logic QF_NRA)
(set-info :source | KeYmaera example: bouncing-ball-inv, node 188
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const h Real)
(declare-const v Real)
(declare-const V Real)
(declare-const g Real)
(declare-const c Real)
(assert (not (=> (and (and (and (and (and (= h 0. ) (= v V )) (> V 0. )) (> g 0. )) (<= 0. c )) (< c 1. )) (>= h 0. ))))
(check-sat)
