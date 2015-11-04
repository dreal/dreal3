(set-logic QF_NRA_ODE)
(declare-fun fact_running_0 () Bool)
(declare-fun fact_stopped_0 () Bool)
(declare-fun fact_engineblown_0 () Bool)
(declare-fun fact_running_1 () Bool)
(declare-fun fact_stopped_1 () Bool)
(declare-fun fact_engineblown_1 () Bool)
(declare-fun happening () Real)
(declare-fun time_0 () Real)
(declare-fun happening_0 () Real)
(declare-fun time_1 () Real)
(declare-fun happening_1 () Real)
(declare-fun happening_2 () Real)
(declare-fun act_startengine_1 () Bool)
(declare-fun act_stopengine_1 () Bool)
(declare-fun process_moving_0 () Bool)
(declare-fun process_moving_1 () Bool)
(declare-fun act_accelerate_1 () Bool)
(declare-fun act_decelerate_1 () Bool)
(declare-fun event_engineexplode_1 () Bool)
(declare-fun func_d_0_0 () Real)
(declare-fun func_d_0_t () Real)
(declare-fun func_v_0_0 () Real)
(declare-fun func_v_0_t () Real)
(declare-fun func_a_0_0 () Real)
(declare-fun func_a_0_t () Real)
(declare-fun func_d_1_0 () Real)
(declare-fun func_d_1_t () Real)
(declare-fun func_d () Real)
(declare-fun func_v_1_0 () Real)
(declare-fun func_v_1_t () Real)
(declare-fun func_v () Real)
(declare-fun func_a_1_0 () Real)
(declare-fun func_a_1_t () Real)
(declare-fun func_a () Real)
(declare-fun delta_accelerate_a_1  () Real)
(declare-fun delta_decelerate_a_1  () Real)
(declare-fun gamma_moving_0_0 () Real)
(declare-fun gamma_moving_0_t () Real)
(declare-fun gamma_moving_1_0 () Real)
(declare-fun gamma_moving_1_t () Real)
(declare-fun gamma_moving () Real)
(define-ode flow_0 ((= d/dt[happening] 1)(= d/dt[func_d] (+ (* gamma_moving func_v) ))(= d/dt[func_v] (+ (* gamma_moving func_a) ))(= d/dt[func_a] 0)(= d/dt[gamma_moving] 0)))
(define-ode flow_1 ((= d/dt[happening] 1)(= d/dt[func_d] (+ (* gamma_moving func_v) ))(= d/dt[func_v] (+ (* gamma_moving func_a) ))(= d/dt[func_a] 0)(= d/dt[gamma_moving] 0)))
(assert (<= 0 time_0))
(assert (<= time_0 1000))
(assert (<= 0 happening_0))
(assert (<= happening_0 1000))
(assert (<= 0 time_1))
(assert (<= time_1 1000))
(assert (<= 0 happening_1))
(assert (<= happening_1 1000))
(assert (<= 0 happening_2))
(assert (<= happening_2 1000))
(assert (<= -10000 func_d_0_0))
(assert (<= func_d_0_0 10000))
(assert (<= -10000 func_d_0_t))
(assert (<= func_d_0_t 10000))
(assert (<= -10000 func_v_0_0))
(assert (<= func_v_0_0 10000))
(assert (<= -10000 func_v_0_t))
(assert (<= func_v_0_t 10000))
(assert (<= -10000 func_a_0_0))
(assert (<= func_a_0_0 10000))
(assert (<= -10000 func_a_0_t))
(assert (<= func_a_0_t 10000))
(assert (<= -10000 func_d_1_0))
(assert (<= func_d_1_0 10000))
(assert (<= -10000 func_d_1_t))
(assert (<= func_d_1_t 10000))
(assert (<= -10000 func_v_1_0))
(assert (<= func_v_1_0 10000))
(assert (<= -10000 func_v_1_t))
(assert (<= func_v_1_t 10000))
(assert (<= -10000 func_a_1_0))
(assert (<= func_a_1_0 10000))
(assert (<= -10000 func_a_1_t))
(assert (<= func_a_1_t 10000))
(assert (<= -10000 delta_accelerate_a_1 ))
(assert (<= delta_accelerate_a_1  10000))
(assert (<= -10000 delta_decelerate_a_1 ))
(assert (<= delta_decelerate_a_1  10000))
(assert (<= gamma_moving_0_0 1))
(assert (>= gamma_moving_0_0 0))
(assert (<= gamma_moving_0_t 1))
(assert (>= gamma_moving_0_t 0))
(assert (<= gamma_moving_1_0 1))
(assert (>= gamma_moving_1_0 0))
(assert (<= gamma_moving_1_t 1))
(assert (>= gamma_moving_1_t 0))
(assert (and

(not fact_engineblown_0) fact_running_0 (not fact_stopped_0) (= func_d_0_0 0)(= func_a_0_0 1)(= func_v_0_0 200)

(= happening_0 0)








(=> act_startengine_1 (and fact_stopped_0))

(=> act_startengine_1 fact_running_1)

(=> act_startengine_1 (not fact_stopped_1))








(=> act_stopengine_1 (and (= func_v_0_t 0) (= func_a_0_t 0) fact_running_0))

(=> act_stopengine_1 fact_stopped_1)

(=> act_stopengine_1 (not fact_running_1))






(=> process_moving_0 (and (and fact_running_0)))(=> (and (and fact_running_0)) process_moving_0)(=> (not process_moving_0)  (or (not (and (and fact_running_0)))))(=> (or (not (and (and fact_running_0)))) (not process_moving_0))

(=> process_moving_0 (= (gamma_moving_0_0) 1))(=> (= (gamma_moving_0_0) 1) process_moving_0)(=> (not process_moving_0)  (= (gamma_moving_0_0) 0))(=> (= (gamma_moving_0_0) 0) (not process_moving_0))

(=> process_moving_0 (= (gamma_moving_0_0) 1))(=> (= (gamma_moving_0_0) 1) process_moving_0)(=> (not process_moving_0)  (= (gamma_moving_0_0) 0))(=> (= (gamma_moving_0_0) 0) (not process_moving_0))



(=> process_moving_1 (and (and fact_running_1)))(=> (and (and fact_running_1)) process_moving_1)(=> (not process_moving_1)  (or (not (and (and fact_running_1)))))(=> (or (not (and (and fact_running_1)))) (not process_moving_1))

(=> process_moving_1 (= (gamma_moving_1_0) 1))(=> (= (gamma_moving_1_0) 1) process_moving_1)(=> (not process_moving_1)  (= (gamma_moving_1_0) 0))(=> (= (gamma_moving_1_0) 0) (not process_moving_1))

(=> process_moving_1 (= (gamma_moving_1_0) 1))(=> (= (gamma_moving_1_0) 1) process_moving_1)(=> (not process_moving_1)  (= (gamma_moving_1_0) 0))(=> (= (gamma_moving_1_0) 0) (not process_moving_1))








(=> act_accelerate_1 (and fact_running_0))

(=> act_accelerate_1  (and (= (delta_accelerate_a_1) 1) (not (= (delta_accelerate_a_1) 0))))(=> (not act_accelerate_1) (and (= (delta_accelerate_a_1) 0) (not (= (delta_accelerate_a_1) 1))))








(=> act_decelerate_1 (and fact_running_0))

(=> act_decelerate_1  (and (= (delta_decelerate_a_1) -1) (not (= (delta_decelerate_a_1) 0))))(=> (not act_decelerate_1) (and (= (delta_decelerate_a_1) 0) (not (= (delta_decelerate_a_1) -1))))








(=> event_engineexplode_1 (or (and fact_running_0 (>= func_v_0_0 200)) (and (and fact_running_0 (>= func_v_0_t 200))(not (and  (>= func_v_0_0 200))) (forall_t 1 [0 time_0] (not (and  (>= func_v_0_t 200)))))))(=> (or (and fact_running_0 (>= func_v_0_0 200)) (and (and fact_running_0 (>= func_v_0_t 200))(not (and  (>= func_v_0_0 200))) (forall_t 1 [0 time_0] (not (and  (>= func_v_0_t 200)))))) event_engineexplode_1)

(=> (and fact_running_0 (>= func_v_0_0 200)) (and  event_engineexplode_1 (= time_0 0)))

(=> event_engineexplode_1 fact_engineblown_1)

(=> event_engineexplode_1 (not fact_running_1))

(=> event_engineexplode_1 (= (func_a_1_0) 0))







(= func_d_1_0 (+ func_d_0_t ))(= func_v_1_0 (+ func_v_0_t ))(=> (not (or event_engineexplode_1 ))(= func_a_1_0 (+ func_a_0_t delta_accelerate_a_1 delta_decelerate_a_1 )))





(= [happening_1 func_d_0_t func_v_0_t func_a_0_t gamma_moving_0_t ] (integral 0. time_0 [happening_0 func_d_0_0 func_v_0_0 func_a_0_0 gamma_moving_0_0 ] flow_0))

(= [happening_2 func_d_1_t func_v_1_t func_a_1_t gamma_moving_1_t ] (integral 0. time_1 [happening_1 func_d_1_0 func_v_1_0 func_a_1_0 gamma_moving_1_0 ] flow_1))





(=> fact_engineblown_0 fact_engineblown_1)(=> (not (or event_engineexplode_1 ))(=> (not fact_engineblown_0) (not fact_engineblown_1)))(=> (not (or event_engineexplode_1 act_stopengine_1 ))(=> fact_running_0 fact_running_1))(=> (not (or act_startengine_1 ))(=> (not fact_running_0) (not fact_running_1)))(=> (not (or act_startengine_1 ))(=> fact_stopped_0 fact_stopped_1))(=> (not (or act_stopengine_1 ))(=> (not fact_stopped_0) (not fact_stopped_1)))





(=> act_accelerate_1 (not event_engineexplode_1))

(=> act_accelerate_1 (not act_startengine_1))
(=> act_accelerate_1 (not act_stopengine_1))
(=> act_decelerate_1 (not event_engineexplode_1))

(=> act_decelerate_1 (not act_startengine_1))
(=> act_decelerate_1 (not act_stopengine_1))
(=> act_startengine_1 (not event_engineexplode_1))
(=> act_startengine_1 (not act_accelerate_1))
(=> act_startengine_1 (not act_decelerate_1))
(=> act_startengine_1 (not act_stopengine_1))
(=> act_stopengine_1 (not event_engineexplode_1))
(=> act_stopengine_1 (not act_accelerate_1))
(=> act_stopengine_1 (not act_decelerate_1))
(=> act_stopengine_1 (not act_startengine_1))



(<= (+ happening_0 0)happening_1)

))
(assert 

(or (and fact_engineblown_1))

)(check-sat)
(exit)
