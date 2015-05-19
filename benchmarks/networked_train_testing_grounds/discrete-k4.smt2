(set-logic QF_NRA_ODE)
(declare-fun time_0 () Real)
(declare-fun time_1 () Real)
(declare-fun time_2 () Real)
(declare-fun time_3 () Real)
(declare-fun time_4 () Real)
(declare-fun sync_la_0 () Bool)
(declare-fun sync_la_1 () Bool)
(declare-fun sync_la_2 () Bool)
(declare-fun sync_la_3 () Bool)
(declare-fun mode_1_0 () Real)
(declare-fun mode_1_1 () Real)
(declare-fun mode_1_2 () Real)
(declare-fun mode_1_3 () Real)
(declare-fun mode_1_4 () Real)
(declare-fun mode_2_0 () Real)
(declare-fun mode_2_1 () Real)
(declare-fun mode_2_2 () Real)
(declare-fun mode_2_3 () Real)
(declare-fun mode_2_4 () Real)
(declare-fun gamma_test_1 () Real)
(declare-fun gamma_test_2 () Real)
(declare-fun gamma_test_3 () Real)
(declare-fun gamma_test2_1 () Real)
(declare-fun gamma_test2_2 () Real)
(declare-fun gamma_test2_3 () Real)
(declare-fun gamma_test_1_0_0 () Real)
(declare-fun gamma_test_1_1_0 () Real)
(declare-fun gamma_test_1_2_0 () Real)
(declare-fun gamma_test_1_3_0 () Real)
(declare-fun gamma_test_1_4_0 () Real)
(declare-fun gamma_test_2_0_0 () Real)
(declare-fun gamma_test_2_1_0 () Real)
(declare-fun gamma_test_2_2_0 () Real)
(declare-fun gamma_test_2_3_0 () Real)
(declare-fun gamma_test_2_4_0 () Real)
(declare-fun gamma_test_3_0_0 () Real)
(declare-fun gamma_test_3_1_0 () Real)
(declare-fun gamma_test_3_2_0 () Real)
(declare-fun gamma_test_3_3_0 () Real)
(declare-fun gamma_test_3_4_0 () Real)
(declare-fun gamma_test2_1_0_0 () Real)
(declare-fun gamma_test2_1_1_0 () Real)
(declare-fun gamma_test2_1_2_0 () Real)
(declare-fun gamma_test2_1_3_0 () Real)
(declare-fun gamma_test2_1_4_0 () Real)
(declare-fun gamma_test2_2_0_0 () Real)
(declare-fun gamma_test2_2_1_0 () Real)
(declare-fun gamma_test2_2_2_0 () Real)
(declare-fun gamma_test2_2_3_0 () Real)
(declare-fun gamma_test2_2_4_0 () Real)
(declare-fun gamma_test2_3_0_0 () Real)
(declare-fun gamma_test2_3_1_0 () Real)
(declare-fun gamma_test2_3_2_0 () Real)
(declare-fun gamma_test2_3_3_0 () Real)
(declare-fun gamma_test2_3_4_0 () Real)
(define-ode flow_0 ((= d/dt[gamma_test_1] 0) (= d/dt[gamma_test_2] 0) (= d/dt[gamma_test_3] 0) (= d/dt[gamma_test2_1] 0) (= d/dt[gamma_test2_2] 0) (= d/dt[gamma_test2_3] 0)))
(assert (<= 0 time_0))
(assert (<= time_0 5))
(assert (<= 0 time_1))
(assert (<= time_1 5))
(assert (<= 0 time_2))
(assert (<= time_2 5))
(assert (<= 0 time_3))
(assert (<= time_3 5))
(assert (<= 0 time_4))
(assert (<= time_4 5))
(assert (<= 1 mode_1_0))
(assert (<= mode_1_0 3))
(assert (<= 1 mode_1_1))
(assert (<= mode_1_1 3))
(assert (<= 1 mode_1_2))
(assert (<= mode_1_2 3))
(assert (<= 1 mode_1_3))
(assert (<= mode_1_3 3))
(assert (<= 1 mode_1_4))
(assert (<= mode_1_4 3))
(assert (<= 1 mode_2_0))
(assert (<= mode_2_0 3))
(assert (<= 1 mode_2_1))
(assert (<= mode_2_1 3))
(assert (<= 1 mode_2_2))
(assert (<= mode_2_2 3))
(assert (<= 1 mode_2_3))
(assert (<= mode_2_3 3))
(assert (<= 1 mode_2_4))
(assert (<= mode_2_4 3))
(assert (<= 0 gamma_test_1_0_0))
(assert (<= gamma_test_1_0_0 1))
(assert (<= 0 gamma_test_1_1_0))
(assert (<= gamma_test_1_1_0 1))
(assert (<= 0 gamma_test_1_2_0))
(assert (<= gamma_test_1_2_0 1))
(assert (<= 0 gamma_test_1_3_0))
(assert (<= gamma_test_1_3_0 1))
(assert (<= 0 gamma_test_1_4_0))
(assert (<= gamma_test_1_4_0 1))
(assert (<= 0 gamma_test_2_0_0))
(assert (<= gamma_test_2_0_0 1))
(assert (<= 0 gamma_test_2_1_0))
(assert (<= gamma_test_2_1_0 1))
(assert (<= 0 gamma_test_2_2_0))
(assert (<= gamma_test_2_2_0 1))
(assert (<= 0 gamma_test_2_3_0))
(assert (<= gamma_test_2_3_0 1))
(assert (<= 0 gamma_test_2_4_0))
(assert (<= gamma_test_2_4_0 1))
(assert (<= 0 gamma_test_3_0_0))
(assert (<= gamma_test_3_0_0 1))
(assert (<= 0 gamma_test_3_1_0))
(assert (<= gamma_test_3_1_0 1))
(assert (<= 0 gamma_test_3_2_0))
(assert (<= gamma_test_3_2_0 1))
(assert (<= 0 gamma_test_3_3_0))
(assert (<= gamma_test_3_3_0 1))
(assert (<= 0 gamma_test_3_4_0))
(assert (<= gamma_test_3_4_0 1))
(assert (<= 0 gamma_test2_1_0_0))
(assert (<= gamma_test2_1_0_0 1))
(assert (<= 0 gamma_test2_1_1_0))
(assert (<= gamma_test2_1_1_0 1))
(assert (<= 0 gamma_test2_1_2_0))
(assert (<= gamma_test2_1_2_0 1))
(assert (<= 0 gamma_test2_1_3_0))
(assert (<= gamma_test2_1_3_0 1))
(assert (<= 0 gamma_test2_1_4_0))
(assert (<= gamma_test2_1_4_0 1))
(assert (<= 0 gamma_test2_2_0_0))
(assert (<= gamma_test2_2_0_0 1))
(assert (<= 0 gamma_test2_2_1_0))
(assert (<= gamma_test2_2_1_0 1))
(assert (<= 0 gamma_test2_2_2_0))
(assert (<= gamma_test2_2_2_0 1))
(assert (<= 0 gamma_test2_2_3_0))
(assert (<= gamma_test2_2_3_0 1))
(assert (<= 0 gamma_test2_2_4_0))
(assert (<= gamma_test2_2_4_0 1))
(assert (<= 0 gamma_test2_3_0_0))
(assert (<= gamma_test2_3_0_0 1))
(assert (<= 0 gamma_test2_3_1_0))
(assert (<= gamma_test2_3_1_0 1))
(assert (<= 0 gamma_test2_3_2_0))
(assert (<= gamma_test2_3_2_0 1))
(assert (<= 0 gamma_test2_3_3_0))
(assert (<= gamma_test2_3_3_0 1))
(assert (<= 0 gamma_test2_3_4_0))
(assert (<= gamma_test2_3_4_0 1))
(assert (and (= mode_2_0 1) (= mode_1_0 1)))
(assert (and (=> (= gamma_test_1_0_0 0) (not (= mode_1_0 1))) (=> (not (= mode_1_0 1)) (= gamma_test_1_0_0 0)) (=> (= gamma_test_1_0_0 1) (= mode_1_0 1)) (=> (= mode_1_0 1) (= gamma_test_1_0_0 1)) (=> (= gamma_test_2_0_0 0) (not (= mode_1_0 2))) (=> (not (= mode_1_0 2)) (= gamma_test_2_0_0 0)) (=> (= gamma_test_2_0_0 1) (= mode_1_0 2)) (=> (= mode_1_0 2) (= gamma_test_2_0_0 1)) (=> (= gamma_test_3_0_0 0) (not (= mode_1_0 3))) (=> (not (= mode_1_0 3)) (= gamma_test_3_0_0 0)) (=> (= gamma_test_3_0_0 1) (= mode_1_0 3)) (=> (= mode_1_0 3) (= gamma_test_3_0_0 1)) (=> (= gamma_test2_1_0_0 0) (not (= mode_2_0 1))) (=> (not (= mode_2_0 1)) (= gamma_test2_1_0_0 0)) (=> (= gamma_test2_1_0_0 1) (= mode_2_0 1)) (=> (= mode_2_0 1) (= gamma_test2_1_0_0 1)) (=> (= gamma_test2_2_0_0 0) (not (= mode_2_0 2))) (=> (not (= mode_2_0 2)) (= gamma_test2_2_0_0 0)) (=> (= gamma_test2_2_0_0 1) (= mode_2_0 2)) (=> (= mode_2_0 2) (= gamma_test2_2_0_0 1)) (=> (= gamma_test2_3_0_0 0) (not (= mode_2_0 3))) (=> (not (= mode_2_0 3)) (= gamma_test2_3_0_0 0)) (=> (= gamma_test2_3_0_0 1) (= mode_2_0 3)) (=> (= mode_2_0 3) (= gamma_test2_3_0_0 1)) (= [gamma_test_1_0_0 gamma_test_2_0_0 gamma_test_3_0_0 gamma_test2_1_0_0 gamma_test2_2_0_0 gamma_test2_3_0_0] (integral 0. time_0 [gamma_test_1_0_0 gamma_test_2_0_0 gamma_test_3_0_0 gamma_test2_1_0_0 gamma_test2_2_0_0 gamma_test2_3_0_0] flow_0)) (=> (= mode_2_0 3) (forall_t 0 [0 time_0] true)) (=> (= mode_2_0 2) (forall_t 0 [0 time_0] true)) (=> (= mode_2_0 1) (forall_t 0 [0 time_0] true)) (=> (= mode_1_0 3) (forall_t 0 [0 time_0] true)) (=> (= mode_1_0 2) (forall_t 0 [0 time_0] true)) (=> (= mode_1_0 1) (forall_t 0 [0 time_0] true)) (or (and sync_la_0 (= mode_2_1 2) (= mode_2_0 3)) (and (not sync_la_0) (= mode_2_1 3) (= mode_2_0 3)) (and sync_la_0 (= mode_2_1 2) (= mode_2_0 2)) (and (not sync_la_0) (= mode_2_1 2) (= mode_2_0 2)) (and sync_la_0 (= mode_2_1 3) (= mode_2_0 1)) (and (not sync_la_0) (= mode_2_1 1) (= mode_2_0 1))) (or (and (not sync_la_0) (= mode_1_1 2) (= mode_1_0 3)) (and (not sync_la_0) (= mode_1_1 3) (= mode_1_0 3)) (and sync_la_0 (= mode_1_1 2) (= mode_1_0 2)) (and (not sync_la_0) (= mode_1_1 2) (= mode_1_0 2)) (and (not sync_la_0) (= mode_1_1 3) (= mode_1_0 1)) (and (not sync_la_0) (= mode_1_1 1) (= mode_1_0 1))) (=> (= gamma_test_1_1_0 0) (not (= mode_1_1 1))) (=> (not (= mode_1_1 1)) (= gamma_test_1_1_0 0)) (=> (= gamma_test_1_1_0 1) (= mode_1_1 1)) (=> (= mode_1_1 1) (= gamma_test_1_1_0 1)) (=> (= gamma_test_2_1_0 0) (not (= mode_1_1 2))) (=> (not (= mode_1_1 2)) (= gamma_test_2_1_0 0)) (=> (= gamma_test_2_1_0 1) (= mode_1_1 2)) (=> (= mode_1_1 2) (= gamma_test_2_1_0 1)) (=> (= gamma_test_3_1_0 0) (not (= mode_1_1 3))) (=> (not (= mode_1_1 3)) (= gamma_test_3_1_0 0)) (=> (= gamma_test_3_1_0 1) (= mode_1_1 3)) (=> (= mode_1_1 3) (= gamma_test_3_1_0 1)) (=> (= gamma_test2_1_1_0 0) (not (= mode_2_1 1))) (=> (not (= mode_2_1 1)) (= gamma_test2_1_1_0 0)) (=> (= gamma_test2_1_1_0 1) (= mode_2_1 1)) (=> (= mode_2_1 1) (= gamma_test2_1_1_0 1)) (=> (= gamma_test2_2_1_0 0) (not (= mode_2_1 2))) (=> (not (= mode_2_1 2)) (= gamma_test2_2_1_0 0)) (=> (= gamma_test2_2_1_0 1) (= mode_2_1 2)) (=> (= mode_2_1 2) (= gamma_test2_2_1_0 1)) (=> (= gamma_test2_3_1_0 0) (not (= mode_2_1 3))) (=> (not (= mode_2_1 3)) (= gamma_test2_3_1_0 0)) (=> (= gamma_test2_3_1_0 1) (= mode_2_1 3)) (=> (= mode_2_1 3) (= gamma_test2_3_1_0 1)) (= [gamma_test_1_1_0 gamma_test_2_1_0 gamma_test_3_1_0 gamma_test2_1_1_0 gamma_test2_2_1_0 gamma_test2_3_1_0] (integral 0. time_1 [gamma_test_1_1_0 gamma_test_2_1_0 gamma_test_3_1_0 gamma_test2_1_1_0 gamma_test2_2_1_0 gamma_test2_3_1_0] flow_0)) (=> (= mode_2_1 3) (forall_t 1 [0 time_1] true)) (=> (= mode_2_1 2) (forall_t 1 [0 time_1] true)) (=> (= mode_2_1 1) (forall_t 1 [0 time_1] true)) (=> (= mode_1_1 3) (forall_t 1 [0 time_1] true)) (=> (= mode_1_1 2) (forall_t 1 [0 time_1] true)) (=> (= mode_1_1 1) (forall_t 1 [0 time_1] true)) (or (and sync_la_1 (= mode_2_2 2) (= mode_2_1 3)) (and (not sync_la_1) (= mode_2_2 3) (= mode_2_1 3)) (and sync_la_1 (= mode_2_2 2) (= mode_2_1 2)) (and (not sync_la_1) (= mode_2_2 2) (= mode_2_1 2)) (and sync_la_1 (= mode_2_2 3) (= mode_2_1 1)) (and (not sync_la_1) (= mode_2_2 1) (= mode_2_1 1))) (or (and (not sync_la_1) (= mode_1_2 2) (= mode_1_1 3)) (and (not sync_la_1) (= mode_1_2 3) (= mode_1_1 3)) (and sync_la_1 (= mode_1_2 2) (= mode_1_1 2)) (and (not sync_la_1) (= mode_1_2 2) (= mode_1_1 2)) (and (not sync_la_1) (= mode_1_2 3) (= mode_1_1 1)) (and (not sync_la_1) (= mode_1_2 1) (= mode_1_1 1))) (=> (= gamma_test_1_2_0 0) (not (= mode_1_2 1))) (=> (not (= mode_1_2 1)) (= gamma_test_1_2_0 0)) (=> (= gamma_test_1_2_0 1) (= mode_1_2 1)) (=> (= mode_1_2 1) (= gamma_test_1_2_0 1)) (=> (= gamma_test_2_2_0 0) (not (= mode_1_2 2))) (=> (not (= mode_1_2 2)) (= gamma_test_2_2_0 0)) (=> (= gamma_test_2_2_0 1) (= mode_1_2 2)) (=> (= mode_1_2 2) (= gamma_test_2_2_0 1)) (=> (= gamma_test_3_2_0 0) (not (= mode_1_2 3))) (=> (not (= mode_1_2 3)) (= gamma_test_3_2_0 0)) (=> (= gamma_test_3_2_0 1) (= mode_1_2 3)) (=> (= mode_1_2 3) (= gamma_test_3_2_0 1)) (=> (= gamma_test2_1_2_0 0) (not (= mode_2_2 1))) (=> (not (= mode_2_2 1)) (= gamma_test2_1_2_0 0)) (=> (= gamma_test2_1_2_0 1) (= mode_2_2 1)) (=> (= mode_2_2 1) (= gamma_test2_1_2_0 1)) (=> (= gamma_test2_2_2_0 0) (not (= mode_2_2 2))) (=> (not (= mode_2_2 2)) (= gamma_test2_2_2_0 0)) (=> (= gamma_test2_2_2_0 1) (= mode_2_2 2)) (=> (= mode_2_2 2) (= gamma_test2_2_2_0 1)) (=> (= gamma_test2_3_2_0 0) (not (= mode_2_2 3))) (=> (not (= mode_2_2 3)) (= gamma_test2_3_2_0 0)) (=> (= gamma_test2_3_2_0 1) (= mode_2_2 3)) (=> (= mode_2_2 3) (= gamma_test2_3_2_0 1)) (= [gamma_test_1_2_0 gamma_test_2_2_0 gamma_test_3_2_0 gamma_test2_1_2_0 gamma_test2_2_2_0 gamma_test2_3_2_0] (integral 0. time_2 [gamma_test_1_2_0 gamma_test_2_2_0 gamma_test_3_2_0 gamma_test2_1_2_0 gamma_test2_2_2_0 gamma_test2_3_2_0] flow_0)) (=> (= mode_2_2 3) (forall_t 2 [0 time_2] true)) (=> (= mode_2_2 2) (forall_t 2 [0 time_2] true)) (=> (= mode_2_2 1) (forall_t 2 [0 time_2] true)) (=> (= mode_1_2 3) (forall_t 2 [0 time_2] true)) (=> (= mode_1_2 2) (forall_t 2 [0 time_2] true)) (=> (= mode_1_2 1) (forall_t 2 [0 time_2] true)) (or (and sync_la_2 (= mode_2_3 2) (= mode_2_2 3)) (and (not sync_la_2) (= mode_2_3 3) (= mode_2_2 3)) (and sync_la_2 (= mode_2_3 2) (= mode_2_2 2)) (and (not sync_la_2) (= mode_2_3 2) (= mode_2_2 2)) (and sync_la_2 (= mode_2_3 3) (= mode_2_2 1)) (and (not sync_la_2) (= mode_2_3 1) (= mode_2_2 1))) (or (and (not sync_la_2) (= mode_1_3 2) (= mode_1_2 3)) (and (not sync_la_2) (= mode_1_3 3) (= mode_1_2 3)) (and sync_la_2 (= mode_1_3 2) (= mode_1_2 2)) (and (not sync_la_2) (= mode_1_3 2) (= mode_1_2 2)) (and (not sync_la_2) (= mode_1_3 3) (= mode_1_2 1)) (and (not sync_la_2) (= mode_1_3 1) (= mode_1_2 1))) (=> (= gamma_test_1_3_0 0) (not (= mode_1_3 1))) (=> (not (= mode_1_3 1)) (= gamma_test_1_3_0 0)) (=> (= gamma_test_1_3_0 1) (= mode_1_3 1)) (=> (= mode_1_3 1) (= gamma_test_1_3_0 1)) (=> (= gamma_test_2_3_0 0) (not (= mode_1_3 2))) (=> (not (= mode_1_3 2)) (= gamma_test_2_3_0 0)) (=> (= gamma_test_2_3_0 1) (= mode_1_3 2)) (=> (= mode_1_3 2) (= gamma_test_2_3_0 1)) (=> (= gamma_test_3_3_0 0) (not (= mode_1_3 3))) (=> (not (= mode_1_3 3)) (= gamma_test_3_3_0 0)) (=> (= gamma_test_3_3_0 1) (= mode_1_3 3)) (=> (= mode_1_3 3) (= gamma_test_3_3_0 1)) (=> (= gamma_test2_1_3_0 0) (not (= mode_2_3 1))) (=> (not (= mode_2_3 1)) (= gamma_test2_1_3_0 0)) (=> (= gamma_test2_1_3_0 1) (= mode_2_3 1)) (=> (= mode_2_3 1) (= gamma_test2_1_3_0 1)) (=> (= gamma_test2_2_3_0 0) (not (= mode_2_3 2))) (=> (not (= mode_2_3 2)) (= gamma_test2_2_3_0 0)) (=> (= gamma_test2_2_3_0 1) (= mode_2_3 2)) (=> (= mode_2_3 2) (= gamma_test2_2_3_0 1)) (=> (= gamma_test2_3_3_0 0) (not (= mode_2_3 3))) (=> (not (= mode_2_3 3)) (= gamma_test2_3_3_0 0)) (=> (= gamma_test2_3_3_0 1) (= mode_2_3 3)) (=> (= mode_2_3 3) (= gamma_test2_3_3_0 1)) (= [gamma_test_1_3_0 gamma_test_2_3_0 gamma_test_3_3_0 gamma_test2_1_3_0 gamma_test2_2_3_0 gamma_test2_3_3_0] (integral 0. time_3 [gamma_test_1_3_0 gamma_test_2_3_0 gamma_test_3_3_0 gamma_test2_1_3_0 gamma_test2_2_3_0 gamma_test2_3_3_0] flow_0)) (=> (= mode_2_3 3) (forall_t 3 [0 time_3] true)) (=> (= mode_2_3 2) (forall_t 3 [0 time_3] true)) (=> (= mode_2_3 1) (forall_t 3 [0 time_3] true)) (=> (= mode_1_3 3) (forall_t 3 [0 time_3] true)) (=> (= mode_1_3 2) (forall_t 3 [0 time_3] true)) (=> (= mode_1_3 1) (forall_t 3 [0 time_3] true)) (or (and sync_la_3 (= mode_2_4 2) (= mode_2_3 3)) (and (not sync_la_3) (= mode_2_4 3) (= mode_2_3 3)) (and sync_la_3 (= mode_2_4 2) (= mode_2_3 2)) (and (not sync_la_3) (= mode_2_4 2) (= mode_2_3 2)) (and sync_la_3 (= mode_2_4 3) (= mode_2_3 1)) (and (not sync_la_3) (= mode_2_4 1) (= mode_2_3 1))) (or (and (not sync_la_3) (= mode_1_4 2) (= mode_1_3 3)) (and (not sync_la_3) (= mode_1_4 3) (= mode_1_3 3)) (and sync_la_3 (= mode_1_4 2) (= mode_1_3 2)) (and (not sync_la_3) (= mode_1_4 2) (= mode_1_3 2)) (and (not sync_la_3) (= mode_1_4 3) (= mode_1_3 1)) (and (not sync_la_3) (= mode_1_4 1) (= mode_1_3 1)))))
(assert (and (=> (= gamma_test_1_4_0 0) (not (= mode_1_4 1))) (=> (not (= mode_1_4 1)) (= gamma_test_1_4_0 0)) (=> (= gamma_test_1_4_0 1) (= mode_1_4 1)) (=> (= mode_1_4 1) (= gamma_test_1_4_0 1)) (=> (= gamma_test_2_4_0 0) (not (= mode_1_4 2))) (=> (not (= mode_1_4 2)) (= gamma_test_2_4_0 0)) (=> (= gamma_test_2_4_0 1) (= mode_1_4 2)) (=> (= mode_1_4 2) (= gamma_test_2_4_0 1)) (=> (= gamma_test_3_4_0 0) (not (= mode_1_4 3))) (=> (not (= mode_1_4 3)) (= gamma_test_3_4_0 0)) (=> (= gamma_test_3_4_0 1) (= mode_1_4 3)) (=> (= mode_1_4 3) (= gamma_test_3_4_0 1)) (=> (= gamma_test2_1_4_0 0) (not (= mode_2_4 1))) (=> (not (= mode_2_4 1)) (= gamma_test2_1_4_0 0)) (=> (= gamma_test2_1_4_0 1) (= mode_2_4 1)) (=> (= mode_2_4 1) (= gamma_test2_1_4_0 1)) (=> (= gamma_test2_2_4_0 0) (not (= mode_2_4 2))) (=> (not (= mode_2_4 2)) (= gamma_test2_2_4_0 0)) (=> (= gamma_test2_2_4_0 1) (= mode_2_4 2)) (=> (= mode_2_4 2) (= gamma_test2_2_4_0 1)) (=> (= gamma_test2_3_4_0 0) (not (= mode_2_4 3))) (=> (not (= mode_2_4 3)) (= gamma_test2_3_4_0 0)) (=> (= gamma_test2_3_4_0 1) (= mode_2_4 3)) (=> (= mode_2_4 3) (= gamma_test2_3_4_0 1)) (= [gamma_test_1_4_0 gamma_test_2_4_0 gamma_test_3_4_0 gamma_test2_1_4_0 gamma_test2_2_4_0 gamma_test2_3_4_0] (integral 0. time_4 [gamma_test_1_4_0 gamma_test_2_4_0 gamma_test_3_4_0 gamma_test2_1_4_0 gamma_test2_2_4_0 gamma_test2_3_4_0] flow_0)) (=> (= mode_2_4 3) (forall_t 4 [0 time_4] true)) (=> (= mode_2_4 2) (forall_t 4 [0 time_4] true)) (=> (= mode_2_4 1) (forall_t 4 [0 time_4] true)) (=> (= mode_1_4 3) (forall_t 4 [0 time_4] true)) (=> (= mode_1_4 2) (forall_t 4 [0 time_4] true)) (=> (= mode_1_4 1) (forall_t 4 [0 time_4] true))))
(assert (and (= mode_2_4 2) (= mode_1_4 2)))
(check-sat)
(exit)