(set-logic QF_NRA)
(set-info :source | KeYmaera example: square_root_floor_dijkstra, node 98
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const p0 Real)
(declare-const q0 Real)
(declare-const r0 Real)
(assert (not (= (* (* p0 p0) q0) (* q0 (+ (* p0 p0) (* q0 (+ (- r0) r0)))) )))
(check-sat)
