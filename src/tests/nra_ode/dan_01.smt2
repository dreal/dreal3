(set-logic QF_NRA_ODE)
(declare-fun refueling_gen_0 () Int)
(declare-fun generator_ran_0 () Int)
(declare-fun available_tank1_0 () Int)
(declare-fun refueling_gen_1 () Int)
(declare-fun generator_ran_1 () Int)
(declare-fun available_tank1_1 () Int)
(declare-fun refueling_gen_2 () Int)
(declare-fun generator_ran_2 () Int)
(declare-fun available_tank1_2 () Int)
(declare-fun refueling_gen_3 () Int)
(declare-fun generator_ran_3 () Int)
(declare-fun available_tank1_3 () Int)
(declare-fun time_0 () Real)
(declare-fun happening_0 () Real)
(declare-fun time_1 () Real)
(declare-fun happening_1 () Real)
(declare-fun time_2 () Real)
(declare-fun happening_2 () Real)
(declare-fun time_3 () Real)
(declare-fun happening_3 () Real)
(declare-fun happening_4 () Real)
(declare-fun generate_gen_status_0 () Int)
(declare-fun duration_generate_gen_1 () Real)
(declare-fun generate_gen_status_1 () Int)
(declare-fun duration_generate_gen_2 () Real)
(declare-fun generate_gen_status_2 () Int)
(declare-fun generate_gen_status_3 () Int)
(declare-fun refuel_gen_tank1_status_0 () Int)
(declare-fun duration_refuel_gen_tank1_1 () Real)
(declare-fun refuel_gen_tank1_status_1 () Int)
(declare-fun duration_refuel_gen_tank1_2 () Real)
(declare-fun refuel_gen_tank1_status_2 () Int)
(declare-fun refuel_gen_tank1_status_3 () Int)
(declare-fun fuellevel_gen_0_0 () Real)
(declare-fun fuellevel_gen_0_t () Real)
(declare-fun capacity_gen_0_0 () Real)
(declare-fun capacity_gen_0_t () Real)
(declare-fun fuellevel_gen_1_0 () Real)
(declare-fun fuellevel_gen_1_t () Real)
(declare-fun capacity_gen_1_0 () Real)
(declare-fun capacity_gen_1_t () Real)
(declare-fun fuellevel_gen_2_0 () Real)
(declare-fun fuellevel_gen_2_t () Real)
(declare-fun capacity_gen_2_0 () Real)
(declare-fun capacity_gen_2_t () Real)
(declare-fun fuellevel_gen_3_0 () Real)
(declare-fun fuellevel_gen_3_t () Real)
(declare-fun fuellevel_gen () Real)
(declare-fun capacity_gen_3_0 () Real)
(declare-fun capacity_gen_3_t () Real)
(declare-fun capacity_gen () Real)
(declare-fun gamma_generate_gen_0_0 () Real)
(declare-fun gamma_generate_gen_0_t () Real)
(declare-fun gamma_refuel_gen_tank1_0_0 () Real)
(declare-fun gamma_refuel_gen_tank1_0_t () Real)
(declare-fun gamma_generate_gen_1_0 () Real)
(declare-fun gamma_generate_gen_1_t () Real)
(declare-fun gamma_refuel_gen_tank1_1_0 () Real)
(declare-fun gamma_refuel_gen_tank1_1_t () Real)
(declare-fun gamma_generate_gen_2_0 () Real)
(declare-fun gamma_generate_gen_2_t () Real)
(declare-fun gamma_refuel_gen_tank1_2_0 () Real)
(declare-fun gamma_refuel_gen_tank1_2_t () Real)
(declare-fun gamma_generate_gen_3_0 () Real)
(declare-fun gamma_generate_gen_3_t () Real)
(declare-fun gamma_generate_gen () Real)
(declare-fun gamma_refuel_gen_tank1_3_0 () Real)
(declare-fun gamma_refuel_gen_tank1_3_t () Real)
(declare-fun gamma_refuel_gen_tank1 () Real)
(declare-fun happening () Real)
(declare-fun fuellevel_gen () Real)
(declare-fun capacity_gen () Real)
(declare-fun gamma_generate_gen () Real)
(declare-fun gamma_refuel_gen_tank1 () Real)
(define-ode flow_0 (
                    (= d/dt[happening] 1)
                    (= d/dt[fuellevel_gen] (+ (* gamma_generate_gen (* -1.0 1)) (* gamma_refuel_gen_tank1 2) ))
                    (= d/dt[capacity_gen] 0)
                    (= d/dt[gamma_generate_gen] 0)
                    (= d/dt[gamma_refuel_gen_tank1] 0)
                    ))
(define-ode flow_1 (
                    (= d/dt[happening] 1)
                    (= d/dt[fuellevel_gen] (+ (* gamma_generate_gen (* -1.0 1)) (* gamma_refuel_gen_tank1 2) ))
                    (= d/dt[capacity_gen] 0)
                    (= d/dt[gamma_generate_gen] 0)
                    (= d/dt[gamma_refuel_gen_tank1] 0)
                    ))
(define-ode flow_2 (
                    (= d/dt[happening] 1)
                    (= d/dt[fuellevel_gen] (+ (* gamma_generate_gen (* -1.0 1)) (* gamma_refuel_gen_tank1 2) ))
                    (= d/dt[capacity_gen] 0)
                    (= d/dt[gamma_generate_gen] 0)
                    (= d/dt[gamma_refuel_gen_tank1] 0)
                    ))
(define-ode flow_3 (
                    (= d/dt[happening] 1)
                    (= d/dt[fuellevel_gen] (+ (* gamma_generate_gen (* -1.0 1)) (* gamma_refuel_gen_tank1 2) ))
                    (= d/dt[capacity_gen] 0)
                    (= d/dt[gamma_generate_gen] 0)
                    (= d/dt[gamma_refuel_gen_tank1] 0)
                    ))
(assert (<= 0 refueling_gen_0))
(assert (<= refueling_gen_0 1))
(assert (<= 0 generator_ran_0))
(assert (<= generator_ran_0 1))
(assert (<= 0 available_tank1_0))
(assert (<= available_tank1_0 1))
(assert (<= 0 refueling_gen_1))
(assert (<= refueling_gen_1 1))
(assert (<= 0 generator_ran_1))
(assert (<= generator_ran_1 1))
(assert (<= 0 available_tank1_1))
(assert (<= available_tank1_1 1))
(assert (<= 0 refueling_gen_2))
(assert (<= refueling_gen_2 1))
(assert (<= 0 generator_ran_2))
(assert (<= generator_ran_2 1))
(assert (<= 0 available_tank1_2))
(assert (<= available_tank1_2 1))
(assert (<= 0 refueling_gen_3))
(assert (<= refueling_gen_3 1))
(assert (<= 0 generator_ran_3))
(assert (<= generator_ran_3 1))
(assert (<= 0 available_tank1_3))
(assert (<= available_tank1_3 1))
(assert (<= 0 time_0))
(assert (<= time_0 1000))
(assert (<= 0 happening_0))
(assert (<= happening_0 1000))
(assert (<= 0 time_1))
(assert (<= time_1 1000))
(assert (<= 0 happening_1))
(assert (<= happening_1 1000))
(assert (<= 0 time_2))
(assert (<= time_2 1000))
(assert (<= 0 happening_2))
(assert (<= happening_2 1000))
(assert (<= 0 time_3))
(assert (<= time_3 1000))
(assert (<= 0 happening_3))
(assert (<= happening_3 1000))
(assert (<= 0 happening_4))
(assert (<= happening_4 1000))
(assert (<= 0 generate_gen_status_0))
(assert (<= generate_gen_status_0 3))
(assert (<= 0 duration_generate_gen_1))
(assert (<= duration_generate_gen_1 1000))
(assert (<= 0 generate_gen_status_1))
(assert (<= generate_gen_status_1 3))
(assert (<= 0 duration_generate_gen_2))
(assert (<= duration_generate_gen_2 1000))
(assert (<= 0 generate_gen_status_2))
(assert (<= generate_gen_status_2 3))
(assert (<= 0 generate_gen_status_3))
(assert (<= generate_gen_status_3 3))
(assert (<= 0 refuel_gen_tank1_status_0))
(assert (<= refuel_gen_tank1_status_0 3))
(assert (<= 0 duration_refuel_gen_tank1_1))
(assert (<= duration_refuel_gen_tank1_1 1000))
(assert (<= 0 refuel_gen_tank1_status_1))
(assert (<= refuel_gen_tank1_status_1 3))
(assert (<= 0 duration_refuel_gen_tank1_2))
(assert (<= duration_refuel_gen_tank1_2 1000))
(assert (<= 0 refuel_gen_tank1_status_2))
(assert (<= refuel_gen_tank1_status_2 3))
(assert (<= 0 refuel_gen_tank1_status_3))
(assert (<= refuel_gen_tank1_status_3 3))
(assert (<= -10000 fuellevel_gen_0_0))
(assert (<= fuellevel_gen_0_0 10000))
(assert (<= -10000 fuellevel_gen_0_t))
(assert (<= fuellevel_gen_0_t 10000))
(assert (<= -10000 capacity_gen_0_0))
(assert (<= capacity_gen_0_0 10000))
(assert (<= -10000 capacity_gen_0_t))
(assert (<= capacity_gen_0_t 10000))
(assert (<= -10000 fuellevel_gen_1_0))
(assert (<= fuellevel_gen_1_0 10000))
(assert (<= -10000 fuellevel_gen_1_t))
(assert (<= fuellevel_gen_1_t 10000))
(assert (<= -10000 capacity_gen_1_0))
(assert (<= capacity_gen_1_0 10000))
(assert (<= -10000 capacity_gen_1_t))
(assert (<= capacity_gen_1_t 10000))
(assert (<= -10000 fuellevel_gen_2_0))
(assert (<= fuellevel_gen_2_0 10000))
(assert (<= -10000 fuellevel_gen_2_t))
(assert (<= fuellevel_gen_2_t 10000))
(assert (<= -10000 capacity_gen_2_0))
(assert (<= capacity_gen_2_0 10000))
(assert (<= -10000 capacity_gen_2_t))
(assert (<= capacity_gen_2_t 10000))
(assert (<= -10000 fuellevel_gen_3_0))
(assert (<= fuellevel_gen_3_0 10000))
(assert (<= -10000 fuellevel_gen_3_t))
(assert (<= fuellevel_gen_3_t 10000))
(assert (<= -10000 capacity_gen_3_0))
(assert (<= capacity_gen_3_0 10000))
(assert (<= -10000 capacity_gen_3_t))
(assert (<= capacity_gen_3_t 10000))
(assert (<= gamma_generate_gen_0_0 1))
(assert (>= gamma_generate_gen_0_0 0))
(assert (<= gamma_generate_gen_0_t 1))
(assert (>= gamma_generate_gen_0_t 0))
(assert (<= gamma_refuel_gen_tank1_0_0 1))
(assert (>= gamma_refuel_gen_tank1_0_0 0))
(assert (<= gamma_refuel_gen_tank1_0_t 1))
(assert (>= gamma_refuel_gen_tank1_0_t 0))
(assert (<= gamma_generate_gen_1_0 1))
(assert (>= gamma_generate_gen_1_0 0))
(assert (<= gamma_generate_gen_1_t 1))
(assert (>= gamma_generate_gen_1_t 0))
(assert (<= gamma_refuel_gen_tank1_1_0 1))
(assert (>= gamma_refuel_gen_tank1_1_0 0))
(assert (<= gamma_refuel_gen_tank1_1_t 1))
(assert (>= gamma_refuel_gen_tank1_1_t 0))
(assert (<= gamma_generate_gen_2_0 1))
(assert (>= gamma_generate_gen_2_0 0))
(assert (<= gamma_generate_gen_2_t 1))
(assert (>= gamma_generate_gen_2_t 0))
(assert (<= gamma_refuel_gen_tank1_2_0 1))
(assert (>= gamma_refuel_gen_tank1_2_0 0))
(assert (<= gamma_refuel_gen_tank1_2_t 1))
(assert (>= gamma_refuel_gen_tank1_2_t 0))
(assert (<= gamma_generate_gen_3_0 1))
(assert (>= gamma_generate_gen_3_0 0))
(assert (<= gamma_generate_gen_3_t 1))
(assert (>= gamma_generate_gen_3_t 0))
(assert (<= gamma_refuel_gen_tank1_3_0 1))
(assert (>= gamma_refuel_gen_tank1_3_0 0))
(assert (<= gamma_refuel_gen_tank1_3_t 1))
(assert (>= gamma_refuel_gen_tank1_3_t 0))
(assert (and(or (= 0 refueling_gen_0) (= 1 refueling_gen_0))(or (not (= 0 refueling_gen_0)) (not (= 1 refueling_gen_0)))(or (= 0 generator_ran_0) (= 1 generator_ran_0))(or (not (= 0 generator_ran_0)) (not (= 1 generator_ran_0)))(or (= 0 available_tank1_0) (= 1 available_tank1_0))(or (not (= 0 available_tank1_0)) (not (= 1 available_tank1_0)))(or (= 0 refueling_gen_1) (= 1 refueling_gen_1))(or (not (= 0 refueling_gen_1)) (not (= 1 refueling_gen_1)))(or (= 0 generator_ran_1) (= 1 generator_ran_1))(or (not (= 0 generator_ran_1)) (not (= 1 generator_ran_1)))(or (= 0 available_tank1_1) (= 1 available_tank1_1))(or (not (= 0 available_tank1_1)) (not (= 1 available_tank1_1)))(or (= 0 refueling_gen_2) (= 1 refueling_gen_2))(or (not (= 0 refueling_gen_2)) (not (= 1 refueling_gen_2)))(or (= 0 generator_ran_2) (= 1 generator_ran_2))(or (not (= 0 generator_ran_2)) (not (= 1 generator_ran_2)))(or (= 0 available_tank1_2) (= 1 available_tank1_2))(or (not (= 0 available_tank1_2)) (not (= 1 available_tank1_2)))(or (= 0 refueling_gen_3) (= 1 refueling_gen_3))(or (not (= 0 refueling_gen_3)) (not (= 1 refueling_gen_3)))(or (= 0 generator_ran_3) (= 1 generator_ran_3))(or (not (= 0 generator_ran_3)) (not (= 1 generator_ran_3)))(or (= 0 available_tank1_3) (= 1 available_tank1_3))(or (not (= 0 available_tank1_3)) (not (= 1 available_tank1_3)))

(= 1 available_tank1_0)(= 0 generator_ran_0)(= 0 refueling_gen_0)(= fuellevel_gen_0_0 960)(= capacity_gen_0_0 1600)(= happening_0 0)



(or (and (= 1 generator_ran_3)))




(= (gamma_generate_gen_0_0) 0)

(or  (= 0 generate_gen_status_0) (= 1 generate_gen_status_0) (= 2 generate_gen_status_0) (= 3 generate_gen_status_0))(not (= 1 generate_gen_status_0))(not (= 2 generate_gen_status_0))(not (= 3 generate_gen_status_0))



(=> (= 1 generate_gen_status_1) (= duration_generate_gen_1 1000))

(=> (and (= 1 generate_gen_status_1) (= 3 generate_gen_status_2)) (= (- happening_2 happening_1) (duration_generate_gen_1)))(=> (and (= 1 generate_gen_status_1) (= 3 generate_gen_status_3) (= 2 generate_gen_status_2)) (= (- happening_3 happening_1) (duration_generate_gen_1)))

(=> (or (= 2 generate_gen_status_1) (= 1 generate_gen_status_1)) (and (forall_t 1 [0  time_1] (>= fuellevel_gen_1_t 0))))(=> (or (= 2 generate_gen_status_2) (= 1 generate_gen_status_2)) (and (forall_t 2 [0  time_2] (>= fuellevel_gen_2_t 0))))

(=> (or (= 0 generate_gen_status_1)) (= (gamma_generate_gen_1_0) 0))(=>  (= (gamma_generate_gen_1_0) 0) (or (= 0 generate_gen_status_1)))(=> (or (= 1 generate_gen_status_1))(= (gamma_generate_gen_1_0) 1))(=> (= (gamma_generate_gen_1_0) 1) (or (= 1 generate_gen_status_1)))

(or  (= 0 generate_gen_status_1) (= 1 generate_gen_status_1) (= 2 generate_gen_status_1) (= 3 generate_gen_status_1))(not (= 2 generate_gen_status_1))(not (= 3 generate_gen_status_1))(=> (= 1 generate_gen_status_1) (or (and (= 2 generate_gen_status_2) )(and (= 3 generate_gen_status_2) )))



(=> (= 1 generate_gen_status_2) (= duration_generate_gen_2 1000))

(=> (and (= 1 generate_gen_status_2) (= 3 generate_gen_status_3)) (= (- happening_3 happening_2) (duration_generate_gen_2)))

(=> (or (= 2 generate_gen_status_2) (= 1 generate_gen_status_2)) (and (forall_t 2 [0  time_2] (>= fuellevel_gen_2_t 0))))



(=> (= 3 generate_gen_status_2) (= 1 generator_ran_2))

(=> (or (= 0 generate_gen_status_2)(= 3 generate_gen_status_2)) (= (gamma_generate_gen_2_0) 0))(=>  (= (gamma_generate_gen_2_0) 0) (or (= 0 generate_gen_status_2)(= 3 generate_gen_status_2)))(=> (or (= 1 generate_gen_status_2)(= 2 generate_gen_status_2))(= (gamma_generate_gen_2_0) 1))(=> (= (gamma_generate_gen_2_0) 1) (or (= 1 generate_gen_status_2)(= 2 generate_gen_status_2)))

(or  (= 0 generate_gen_status_2) (= 1 generate_gen_status_2) (= 2 generate_gen_status_2) (= 3 generate_gen_status_2))(=> (= 1 generate_gen_status_2) (or (and (= 3 generate_gen_status_3) )))(=> (= 2 generate_gen_status_2) (or (and (= 3 generate_gen_status_3) )))(=> (= 3 generate_gen_status_2) (or (and (= 1 generate_gen_status_1) )))(=> (= 2 generate_gen_status_2) (or (and (= 1 generate_gen_status_1) )))



(=> (= 3 generate_gen_status_3) (= 1 generator_ran_3))

(= (gamma_generate_gen_3_0) 0)

(or  (= 0 generate_gen_status_3) (= 1 generate_gen_status_3) (= 2 generate_gen_status_3) (= 3 generate_gen_status_3))(not (= 1 generate_gen_status_3))(not (= 2 generate_gen_status_3))(=> (= 3 generate_gen_status_3) (or (and (= 2 generate_gen_status_2) )(and (= 1 generate_gen_status_2) )))




(= (gamma_refuel_gen_tank1_0_0) 0)

(or  (= 0 refuel_gen_tank1_status_0) (= 1 refuel_gen_tank1_status_0) (= 2 refuel_gen_tank1_status_0) (= 3 refuel_gen_tank1_status_0))(not (= 1 refuel_gen_tank1_status_0))(not (= 2 refuel_gen_tank1_status_0))(not (= 3 refuel_gen_tank1_status_0))



(=> (= 1 refuel_gen_tank1_status_1) (= duration_refuel_gen_tank1_1 20))

(=> (and (= 1 refuel_gen_tank1_status_1) (= 3 refuel_gen_tank1_status_2)) (= (- happening_2 happening_1) (duration_refuel_gen_tank1_1)))(=> (and (= 1 refuel_gen_tank1_status_1) (= 3 refuel_gen_tank1_status_3) (= 2 refuel_gen_tank1_status_2)) (= (- happening_3 happening_1) (duration_refuel_gen_tank1_1)))

(=> (= 1 refuel_gen_tank1_status_1) (and (= 1 available_tank1_0) ))

(=> (or (= 2 refuel_gen_tank1_status_1) (= 1 refuel_gen_tank1_status_1)) (and (forall_t 1 [0  time_1] (and  (< fuellevel_gen_1_t capacity_gen_1_t)))))(=> (or (= 2 refuel_gen_tank1_status_2) (= 1 refuel_gen_tank1_status_2)) (and (forall_t 2 [0  time_2] (and  (< fuellevel_gen_2_t capacity_gen_2_t)))))

(=> (= 1 refuel_gen_tank1_status_1) (= 0 available_tank1_1))

(=> (or (= 0 refuel_gen_tank1_status_1)) (= (gamma_refuel_gen_tank1_1_0) 0))(=>  (= (gamma_refuel_gen_tank1_1_0) 0) (or (= 0 refuel_gen_tank1_status_1)))(=> (or (= 1 refuel_gen_tank1_status_1))(= (gamma_refuel_gen_tank1_1_0) 1))(=> (= (gamma_refuel_gen_tank1_1_0) 1) (or (= 1 refuel_gen_tank1_status_1)))

(=> (= 1 refuel_gen_tank1_status_1) (= 1 refueling_gen_1))

(or  (= 0 refuel_gen_tank1_status_1) (= 1 refuel_gen_tank1_status_1) (= 2 refuel_gen_tank1_status_1) (= 3 refuel_gen_tank1_status_1))(not (= 2 refuel_gen_tank1_status_1))(not (= 3 refuel_gen_tank1_status_1))(=> (= 1 refuel_gen_tank1_status_1) (or (and (= 2 refuel_gen_tank1_status_2) )(and (= 3 refuel_gen_tank1_status_2) )))



(=> (= 1 refuel_gen_tank1_status_2) (= duration_refuel_gen_tank1_2 20))

(=> (and (= 1 refuel_gen_tank1_status_2) (= 3 refuel_gen_tank1_status_3)) (= (- happening_3 happening_2) (duration_refuel_gen_tank1_2)))

(=> (= 1 refuel_gen_tank1_status_2) (and (= 1 available_tank1_1) ))

(=> (or (= 2 refuel_gen_tank1_status_2) (= 1 refuel_gen_tank1_status_2)) (and (forall_t 2 [0  time_2] (and  (< fuellevel_gen_2_t capacity_gen_2_t)))))



(=> (= 3 refuel_gen_tank1_status_2) (= 0 refueling_gen_2))

(=> (= 1 refuel_gen_tank1_status_2) (= 0 available_tank1_2))

(=> (or (= 0 refuel_gen_tank1_status_2)(= 3 refuel_gen_tank1_status_2)) (= (gamma_refuel_gen_tank1_2_0) 0))(=>  (= (gamma_refuel_gen_tank1_2_0) 0) (or (= 0 refuel_gen_tank1_status_2)(= 3 refuel_gen_tank1_status_2)))(=> (or (= 1 refuel_gen_tank1_status_2)(= 2 refuel_gen_tank1_status_2))(= (gamma_refuel_gen_tank1_2_0) 1))(=> (= (gamma_refuel_gen_tank1_2_0) 1) (or (= 1 refuel_gen_tank1_status_2)(= 2 refuel_gen_tank1_status_2)))

(=> (= 1 refuel_gen_tank1_status_2) (= 1 refueling_gen_2))

(or  (= 0 refuel_gen_tank1_status_2) (= 1 refuel_gen_tank1_status_2) (= 2 refuel_gen_tank1_status_2) (= 3 refuel_gen_tank1_status_2))(=> (= 1 refuel_gen_tank1_status_2) (or (and (= 3 refuel_gen_tank1_status_3) )))(=> (= 2 refuel_gen_tank1_status_2) (or (and (= 3 refuel_gen_tank1_status_3) )))(=> (= 3 refuel_gen_tank1_status_2) (or (and (= 1 refuel_gen_tank1_status_1) )))(=> (= 2 refuel_gen_tank1_status_2) (or (and (= 1 refuel_gen_tank1_status_1) )))



(=> (= 3 refuel_gen_tank1_status_3) (= 0 refueling_gen_3))

(= (gamma_refuel_gen_tank1_3_0) 0)

(or  (= 0 refuel_gen_tank1_status_3) (= 1 refuel_gen_tank1_status_3) (= 2 refuel_gen_tank1_status_3) (= 3 refuel_gen_tank1_status_3))(not (= 1 refuel_gen_tank1_status_3))(not (= 2 refuel_gen_tank1_status_3))(=> (= 3 refuel_gen_tank1_status_3) (or (and (= 2 refuel_gen_tank1_status_2) )(and (= 1 refuel_gen_tank1_status_2) )))







(= fuellevel_gen_1_0 (+ fuellevel_gen_0_t ))(= capacity_gen_1_0 (+ capacity_gen_0_t ))

(= fuellevel_gen_2_0 (+ fuellevel_gen_1_t ))(= capacity_gen_2_0 (+ capacity_gen_1_t ))

(= fuellevel_gen_3_0 (+ fuellevel_gen_2_t ))(= capacity_gen_3_0 (+ capacity_gen_2_t ))





(or (and (= time_0 0) (= happening_0 happening_1)(= fuellevel_gen_0_t fuellevel_gen_0_0) (= capacity_gen_0_t capacity_gen_0_0) (= gamma_generate_gen_0_t gamma_generate_gen_0_0) (= gamma_refuel_gen_tank1_0_t gamma_refuel_gen_tank1_0_0) ) (= [happening_1 fuellevel_gen_0_t capacity_gen_0_t gamma_generate_gen_0_t gamma_refuel_gen_tank1_0_t ] (integral 0. time_0 [happening_0 fuellevel_gen_0_0 capacity_gen_0_0 gamma_generate_gen_0_0 gamma_refuel_gen_tank1_0_0 ] flow_0)))

(or (and (= time_1 0) (= happening_1 happening_2)(= fuellevel_gen_1_t fuellevel_gen_1_0) (= capacity_gen_1_t capacity_gen_1_0) (= gamma_generate_gen_1_t gamma_generate_gen_1_0) (= gamma_refuel_gen_tank1_1_t gamma_refuel_gen_tank1_1_0) ) (= [happening_2 fuellevel_gen_1_t capacity_gen_1_t gamma_generate_gen_1_t gamma_refuel_gen_tank1_1_t ] (integral 0. time_1 [happening_1 fuellevel_gen_1_0 capacity_gen_1_0 gamma_generate_gen_1_0 gamma_refuel_gen_tank1_1_0 ] flow_1)))

(or (and (= time_2 0) (= happening_2 happening_3)(= fuellevel_gen_2_t fuellevel_gen_2_0) (= capacity_gen_2_t capacity_gen_2_0) (= gamma_generate_gen_2_t gamma_generate_gen_2_0) (= gamma_refuel_gen_tank1_2_t gamma_refuel_gen_tank1_2_0) ) (= [happening_3 fuellevel_gen_2_t capacity_gen_2_t gamma_generate_gen_2_t gamma_refuel_gen_tank1_2_t ] (integral 0. time_2 [happening_2 fuellevel_gen_2_0 capacity_gen_2_0 gamma_generate_gen_2_0 gamma_refuel_gen_tank1_2_0 ] flow_2)))

(or (and (= time_3 0) (= happening_3 happening_4)(= fuellevel_gen_3_t fuellevel_gen_3_0) (= capacity_gen_3_t capacity_gen_3_0) (= gamma_generate_gen_3_t gamma_generate_gen_3_0) (= gamma_refuel_gen_tank1_3_t gamma_refuel_gen_tank1_3_0) ) (= [happening_4 fuellevel_gen_3_t capacity_gen_3_t gamma_generate_gen_3_t gamma_refuel_gen_tank1_3_t ] (integral 0. time_3 [happening_3 fuellevel_gen_3_0 capacity_gen_3_0 gamma_generate_gen_3_0 gamma_refuel_gen_tank1_3_0 ] flow_3)))





(=> (not (or (= 1 refuel_gen_tank1_status_1)))(=> (= 1 available_tank1_0) (= 1 available_tank1_1)))(=> (= 0 available_tank1_0) (= 0 available_tank1_1))(=> (= 1 generator_ran_0) (= 1 generator_ran_1))(=> (= 0 generator_ran_0) (= 0 generator_ran_1))(=> (= 1 refueling_gen_0) (= 1 refueling_gen_1))(=> (not (or (= 1 refuel_gen_tank1_status_1)))(=> (= 0 refueling_gen_0) (= 0 refueling_gen_1)))

(=> (not (or (= 1 refuel_gen_tank1_status_2)))(=> (= 1 available_tank1_1) (= 1 available_tank1_2)))(=> (= 0 available_tank1_1) (= 0 available_tank1_2))(=> (= 1 generator_ran_1) (= 1 generator_ran_2))(=> (not (or (= 3 generate_gen_status_2)))(=> (= 0 generator_ran_1) (= 0 generator_ran_2)))(=> (not (or (= 3 refuel_gen_tank1_status_2)))(=> (= 1 refueling_gen_1) (= 1 refueling_gen_2)))(=> (not (or (= 1 refuel_gen_tank1_status_2)))(=> (= 0 refueling_gen_1) (= 0 refueling_gen_2)))

(=> (= 1 available_tank1_2) (= 1 available_tank1_3))(=> (= 0 available_tank1_2) (= 0 available_tank1_3))(=> (= 1 generator_ran_2) (= 1 generator_ran_3))(=> (not (or (= 3 generate_gen_status_3)))(=> (= 0 generator_ran_2) (= 0 generator_ran_3)))(=> (not (or (= 3 refuel_gen_tank1_status_3)))(=> (= 1 refueling_gen_2) (= 1 refueling_gen_3)))(=> (= 0 refueling_gen_2) (= 0 refueling_gen_3))



(<= happening_0 happening_1)(<= happening_1 happening_2)(<= happening_2 happening_3)

))
(check-sat)
(exit)
