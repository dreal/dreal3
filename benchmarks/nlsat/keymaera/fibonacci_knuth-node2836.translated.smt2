(set-logic QF_NRA)
(declare-fun ruscore2dollarsk!1 () Real)
(declare-fun quscore2dollarsk!0 () Real)
(assert (= (+ (* quscore2dollarsk!0
                 quscore2dollarsk!0
                 quscore2dollarsk!0
                 quscore2dollarsk!0)
              (* 2.0
                 quscore2dollarsk!0
                 quscore2dollarsk!0
                 quscore2dollarsk!0
                 ruscore2dollarsk!1)
              (* ruscore2dollarsk!1
                 ruscore2dollarsk!1
                 ruscore2dollarsk!1
                 ruscore2dollarsk!1))
           (+ 1.0
              (* quscore2dollarsk!0
                 quscore2dollarsk!0
                 ruscore2dollarsk!1
                 ruscore2dollarsk!1)
              (* 2.0
                 quscore2dollarsk!0
                 ruscore2dollarsk!1
                 ruscore2dollarsk!1
                 ruscore2dollarsk!1))))
(assert (not (= (+ (* ruscore2dollarsk!1
                      ruscore2dollarsk!1
                      ruscore2dollarsk!1
                      ruscore2dollarsk!1)
                   (* 2.0
                      ruscore2dollarsk!1
                      ruscore2dollarsk!1
                      ruscore2dollarsk!1
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0))
                   (* (+ ruscore2dollarsk!1 quscore2dollarsk!0)
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0)
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0)
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0)))
                (+ 1.0
                   (* ruscore2dollarsk!1
                      ruscore2dollarsk!1
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0)
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0))
                   (* 2.0
                      ruscore2dollarsk!1
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0)
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0)
                      (+ ruscore2dollarsk!1 quscore2dollarsk!0))))))
(check-sat)
