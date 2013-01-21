(set-logic QF_NRA)
(declare-fun vuscore2dollarsk_5 () Real)
(declare-fun t1uscore0dollarsk_0 () Real)
(declare-fun stuscore2dollarsk_1 () Real)
(declare-fun tuscore2dollarsk_2 () Real)
(declare-fun suscore2dollarsk_3 () Real)
(declare-fun zuscore2dollarsk_4 () Real)
(assert (= (+ (* 10.0 t1uscore0dollarsk_0) vuscore2dollarsk_5) 200.0))
(assert (>= t1uscore0dollarsk_0 0.0))
(assert (= stuscore2dollarsk_1 0.0))
(assert (= zuscore2dollarsk_4
           (+ (* 4000.0 suscore2dollarsk_3)
              (* tuscore2dollarsk_2
                 tuscore2dollarsk_2
                 (+ 5.0 (* (- 5.0) stuscore2dollarsk_1)))
              (* stuscore2dollarsk_1
                 (+ 2000.0
                    (* 200.0 tuscore2dollarsk_2)
                    (* (- 5.0) tuscore2dollarsk_2 tuscore2dollarsk_2))))))
(assert (>= tuscore2dollarsk_2 0.0))
(assert (>= suscore2dollarsk_3 0.0))
(assert (>= vuscore2dollarsk_5 0.0))
(assert (>= zuscore2dollarsk_4 0.0))
(assert (= vuscore2dollarsk_5
           (+ (* tuscore2dollarsk_2 (+ 10.0 (* (- 10.0) stuscore2dollarsk_1)))
              (* stuscore2dollarsk_1 (+ 200.0 (* (- 10.0) tuscore2dollarsk_2))))))
(assert (not (= (+ (* 5.0 t1uscore0dollarsk_0 t1uscore0dollarsk_0)
                   (* t1uscore0dollarsk_0 vuscore2dollarsk_5)
                   zuscore2dollarsk_4)
                (+ (* 4000.0 suscore2dollarsk_3)
                   (* (+ t1uscore0dollarsk_0 tuscore2dollarsk_2)
                      (+ t1uscore0dollarsk_0 tuscore2dollarsk_2)
                      (+ 5.0 (* (- 5.0) stuscore2dollarsk_1)))
                   (* stuscore2dollarsk_1
                      (+ 2000.0
                         (* 200.0 t1uscore0dollarsk_0)
                         (* 200.0 tuscore2dollarsk_2)
                         (* (- 5.0)
                            (+ t1uscore0dollarsk_0 tuscore2dollarsk_2)
                            (+ t1uscore0dollarsk_0 tuscore2dollarsk_2))))))))
(check-sat)
(exit)
