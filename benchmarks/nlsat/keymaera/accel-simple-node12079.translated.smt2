(set-logic QF_NRA)
(declare-fun vuscore2dollarsk!5 () Real)
(declare-fun t3uscore0dollarsk!0 () Real)
(declare-fun stuscore2dollarsk!1 () Real)
(declare-fun tuscore2dollarsk!2 () Real)
(declare-fun suscore2dollarsk!3 () Real)
(declare-fun zuscore2dollarsk!4 () Real)
(assert (= (+ (* (- 10.0) t3uscore0dollarsk!0) vuscore2dollarsk!5) 0.0))
(assert (>= t3uscore0dollarsk!0 0.0))
(assert (= stuscore2dollarsk!1 1.0))
(assert (= zuscore2dollarsk!4
           (+ (* 4000.0 suscore2dollarsk!3)
              (* tuscore2dollarsk!2
                 tuscore2dollarsk!2
                 (+ 5.0 (* (- 5.0) stuscore2dollarsk!1)))
              (* stuscore2dollarsk!1
                 (+ 2000.0
                    (* 200.0 tuscore2dollarsk!2)
                    (* (- 5.0) tuscore2dollarsk!2 tuscore2dollarsk!2))))))
(assert (>= tuscore2dollarsk!2 0.0))
(assert (>= suscore2dollarsk!3 0.0))
(assert (>= vuscore2dollarsk!5 0.0))
(assert (>= zuscore2dollarsk!4 0.0))
(assert (= vuscore2dollarsk!5
           (+ (* tuscore2dollarsk!2 (+ 10.0 (* (- 10.0) stuscore2dollarsk!1)))
              (* stuscore2dollarsk!1 (+ 200.0 (* (- 10.0) tuscore2dollarsk!2))))))
(assert (not (= (+ (* (- 10.0) t3uscore0dollarsk!0) vuscore2dollarsk!5)
                (+ (* (+ t3uscore0dollarsk!0 tuscore2dollarsk!2)
                      (+ 10.0 (* (- 10.0) stuscore2dollarsk!1)))
                   (* stuscore2dollarsk!1
                      (+ 200.0
                         (* (- 10.0) t3uscore0dollarsk!0)
                         (* (- 10.0) tuscore2dollarsk!2)))))))
(check-sat)
(exit)
