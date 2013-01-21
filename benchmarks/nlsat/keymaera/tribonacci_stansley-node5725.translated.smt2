(set-logic QF_NRA)
(declare-fun ruscore2dollarsk_1 () Real)
(declare-fun buscore2dollarsk_2 () Real)
(declare-fun auscore2dollarsk_0 () Real)
(assert (= (+ (* 2.0 auscore2dollarsk_0 auscore2dollarsk_0 auscore2dollarsk_0)
              (* 2.0 auscore2dollarsk_0 auscore2dollarsk_0 buscore2dollarsk_2)
              (* 2.0 auscore2dollarsk_0 buscore2dollarsk_2 buscore2dollarsk_2)
              (* buscore2dollarsk_2 buscore2dollarsk_2 buscore2dollarsk_2)
              (* (- 2.0)
                 auscore2dollarsk_0
                 buscore2dollarsk_2
                 ruscore2dollarsk_1)
              (* buscore2dollarsk_2 buscore2dollarsk_2 ruscore2dollarsk_1)
              (* (- 2.0)
                 auscore2dollarsk_0
                 ruscore2dollarsk_1
                 ruscore2dollarsk_1)
              (* (- 1.0)
                 buscore2dollarsk_2
                 ruscore2dollarsk_1
                 ruscore2dollarsk_1)
              (* ruscore2dollarsk_1 ruscore2dollarsk_1 ruscore2dollarsk_1))
           1.0))
(assert (not (= (+ (* 2.0 ruscore2dollarsk_1 ruscore2dollarsk_1 ruscore2dollarsk_1)
                   (* 2.0
                      auscore2dollarsk_0
                      ruscore2dollarsk_1
                      ruscore2dollarsk_1)
                   (* 2.0
                      auscore2dollarsk_0
                      auscore2dollarsk_0
                      ruscore2dollarsk_1)
                   (* auscore2dollarsk_0 auscore2dollarsk_0 auscore2dollarsk_0)
                   (* (- 2.0)
                      auscore2dollarsk_0
                      ruscore2dollarsk_1
                      (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2))
                   (* auscore2dollarsk_0
                      auscore2dollarsk_0
                      (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2))
                   (* (- 2.0)
                      ruscore2dollarsk_1
                      (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2)
                      (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2))
                   (* (- 1.0)
                      auscore2dollarsk_0
                      (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2)
                      (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2))
                   (* (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2)
                      (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2)
                      (+ ruscore2dollarsk_1
                         auscore2dollarsk_0
                         buscore2dollarsk_2)))
                1.0)))
(check-sat)
(exit)
