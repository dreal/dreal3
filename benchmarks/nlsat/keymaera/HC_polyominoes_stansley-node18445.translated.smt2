(set-logic QF_NRA)
(declare-fun ruscore2dollarsk!2 () Real)
(declare-fun buscore2dollarsk!3 () Real)
(declare-fun auscore2dollarsk!1 () Real)
(declare-fun guscore2dollarsk!0 () Real)
(assert (= (+ (* (- (/ 1.0 16.0)) guscore2dollarsk!0)
              (* (- 31.0)
                 auscore2dollarsk!1
                 auscore2dollarsk!1
                 auscore2dollarsk!1)
              (* 69.0 auscore2dollarsk!1 auscore2dollarsk!1 buscore2dollarsk!3)
              (* (- 56.0)
                 auscore2dollarsk!1
                 buscore2dollarsk!3
                 buscore2dollarsk!3)
              (* 16.0 buscore2dollarsk!3 buscore2dollarsk!3 buscore2dollarsk!3)
              (* 32.0 auscore2dollarsk!1 auscore2dollarsk!1 ruscore2dollarsk!2)
              (* (- 47.0)
                 auscore2dollarsk!1
                 buscore2dollarsk!3
                 ruscore2dollarsk!2)
              (* 20.0 buscore2dollarsk!3 buscore2dollarsk!3 ruscore2dollarsk!2)
              (* (- 10.0)
                 auscore2dollarsk!1
                 ruscore2dollarsk!2
                 ruscore2dollarsk!2)
              (* 7.0 buscore2dollarsk!3 ruscore2dollarsk!2 ruscore2dollarsk!2)
              (* ruscore2dollarsk!2 ruscore2dollarsk!2 ruscore2dollarsk!2))
           0.0))
(assert (let ((a!1 (+ (* 5.0 ruscore2dollarsk!2)
                      (* (- 7.0) auscore2dollarsk!1)
                      (* 4.0 buscore2dollarsk!3))))
          (not (= (+ (* (- (/ 1.0 4.0)) guscore2dollarsk!0)
                     (* (- 31.0)
                        ruscore2dollarsk!2
                        ruscore2dollarsk!2
                        ruscore2dollarsk!2)
                     (* 69.0
                        auscore2dollarsk!1
                        ruscore2dollarsk!2
                        ruscore2dollarsk!2)
                     (* (- 56.0)
                        auscore2dollarsk!1
                        auscore2dollarsk!1
                        ruscore2dollarsk!2)
                     (* 16.0
                        auscore2dollarsk!1
                        auscore2dollarsk!1
                        auscore2dollarsk!1)
                     (* 32.0 ruscore2dollarsk!2 ruscore2dollarsk!2 a!1)
                     (* (- 47.0) auscore2dollarsk!1 ruscore2dollarsk!2 a!1)
                     (* 20.0 auscore2dollarsk!1 auscore2dollarsk!1 a!1)
                     (* (- 10.0) ruscore2dollarsk!2 a!1 a!1)
                     (* 7.0 auscore2dollarsk!1 a!1 a!1)
                     (* a!1 a!1 a!1))
                  0.0))))
(check-sat)
(exit)
