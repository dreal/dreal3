(set-logic QF_NRA)
(set-info :source | KeYmaera example: controllability-lemma-disturbed, node 799
Andre Platzer and Jan-David Quesel. European Train Control System: A case study in formal verification. In Karin Breitman and Ana Cavalcanti, editors, 11th International Conference on Formal Engineering Methods, ICFEM, Rio de Janeiro, Brasil, Proceedings, volume 5885 of LNCS, pages 246(- 265.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun z () Real)
(declare-fun m () Real)
(declare-fun v () Real)
(declare-fun d () Real)
(declare-fun b () Real)
(declare-fun u () Real)
(declare-fun l () Real)
(assert (not (implies (and (and (and (and (and (and (and (>= (+ z (* (- 1) m)) 0) (<= (+ (* v v) (* (- 1) (* d d)) (* 2 (* z b)) (* (- 2) (* m b)) (* (- 2) (* z u)) (* 2 (* m u))) 0)) (>= v 0)) (>= d 0)) (not (<= (+ b (* (- 1) u)) 0))) (>= u 0)) (>= l 0)) (<= (+ z (* (- 1) m)) 0)) (<= (+ v (* (- 1) d)) 0))))
(check-sat)
