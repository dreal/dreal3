(set-logic QF_NRA)
(set-info :source | KeYmaera example: bouncing-ball-inv, node 188
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun h () Real)
(declare-fun v () Real)
(declare-fun V () Real)
(declare-fun g () Real)
(declare-fun c () Real)
(assert (not (implies (and (and (and (and (and (= h 0) (= (+ v (* (- 1) V)) 0)) (not (<= V 0))) (not (<= g 0))) (<= (* (- 1) c) 0)) (not (>= c 1))) (>= h 0))))
(check-sat)
