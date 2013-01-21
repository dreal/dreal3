(set-logic QF_NRA)
(declare-fun stuscore2dollarsk!0 () Real)
(declare-fun vuscore2dollarsk!4 () Real)
(declare-fun tuscore2dollarsk!1 () Real)
(declare-fun suscore2dollarsk!2 () Real)
(declare-fun zuscore2dollarsk!3 () Real)
(assert (= stuscore2dollarsk!0 1.0))
(assert (= vuscore2dollarsk!4 0.0))
(assert (= zuscore2dollarsk!3
           (+ (* 4000.0 suscore2dollarsk!2)
              (* tuscore2dollarsk!1
                 tuscore2dollarsk!1
                 (+ 5.0 (* (- 5.0) stuscore2dollarsk!0)))
              (* stuscore2dollarsk!0
                 (+ 2000.0
                    (* 200.0 tuscore2dollarsk!1)
                    (* (- 5.0) tuscore2dollarsk!1 tuscore2dollarsk!1))))))
(assert (>= tuscore2dollarsk!1 0.0))
(assert (>= suscore2dollarsk!2 0.0))
(assert (>= vuscore2dollarsk!4 0.0))
(assert (>= zuscore2dollarsk!3 0.0))
(assert (= vuscore2dollarsk!4
           (+ (* tuscore2dollarsk!1 (+ 10.0 (* (- 10.0) stuscore2dollarsk!0)))
              (* stuscore2dollarsk!0 (+ 200.0 (* (- 10.0) tuscore2dollarsk!1))))))
(assert (not (>= suscore2dollarsk!2 (- 1.0))))
(check-sat)
(exit)
