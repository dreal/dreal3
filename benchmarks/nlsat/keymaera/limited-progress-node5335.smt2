(set-logic QF_NRA)
(set-info :source | KeYmaera example: limited-progress, node 533
Andre Platzer and Edmund M. Clarke. Formal verification of curved flight collision avoidance maneuvers: A case study. In Ana Cavalcanti and Dennis Dams, editors, 16th International Symposium on Formal Methods, FM, Eindhoven, Netherlands, Proceedings, volume 5850 of LNCS, pages 547(- 562.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const b Real)
(declare-const d1 Real)
(declare-const d2 Real)
(declare-const x1 Real)
(assert (not (=> (and (>= b 0. ) (<= (+ (* d1 d1) (* d2 d2)) (* b b) )) (<= 0. (- x1 x1) ))))
(check-sat)
