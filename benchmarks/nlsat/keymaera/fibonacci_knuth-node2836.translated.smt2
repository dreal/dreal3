(set-logic QF_NRA)
(declare-fun ruscore2dollarsk_1 () Real)
(declare-fun quscore2dollarsk_0 () Real)
(assert (= (+ (* quscore2dollarsk_0
                 quscore2dollarsk_0
                 quscore2dollarsk_0
                 quscore2dollarsk_0)
              (* 2.0
                 quscore2dollarsk_0
                 quscore2dollarsk_0
                 quscore2dollarsk_0
                 ruscore2dollarsk_1)
              (* ruscore2dollarsk_1
                 ruscore2dollarsk_1
                 ruscore2dollarsk_1
                 ruscore2dollarsk_1))
           (+ 1.0
              (* quscore2dollarsk_0
                 quscore2dollarsk_0
                 ruscore2dollarsk_1
                 ruscore2dollarsk_1)
              (* 2.0
                 quscore2dollarsk_0
                 ruscore2dollarsk_1
                 ruscore2dollarsk_1
                 ruscore2dollarsk_1))))
(assert (not (= (+ (* ruscore2dollarsk_1
                      ruscore2dollarsk_1
                      ruscore2dollarsk_1
                      ruscore2dollarsk_1)
                   (* 2.0
                      ruscore2dollarsk_1
                      ruscore2dollarsk_1
                      ruscore2dollarsk_1
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0))
                   (* (+ ruscore2dollarsk_1 quscore2dollarsk_0)
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0)
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0)
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0)))
                (+ 1.0
                   (* ruscore2dollarsk_1
                      ruscore2dollarsk_1
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0)
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0))
                   (* 2.0
                      ruscore2dollarsk_1
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0)
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0)
                      (+ ruscore2dollarsk_1 quscore2dollarsk_0))))))
(check-sat)
(exit)
