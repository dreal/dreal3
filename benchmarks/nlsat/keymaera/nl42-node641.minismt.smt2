(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl42, node 64
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun d () Real)
(declare-fun c () Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (not (implies (and (and (not (>= (* (- 1) (* d c)) 0)) (not (>= (* (- 1) (* c a)) 0))) (not (>= (* (- 1) (* a b)) 0))) (not (>= (* (- 1) (* d b)) 0)))))
(check-sat)
