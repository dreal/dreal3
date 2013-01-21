(set-logic QF_NRA)
(declare-fun ruscore2dollarsk_2 () Real)
(declare-fun buscore2dollarsk_3 () Real)
(declare-fun auscore2dollarsk_1 () Real)
(declare-fun guscore2dollarsk_0 () Real)
(assert (= (+ (* (- (/ 1.0 16.0)) guscore2dollarsk_0)
              (* (- 31.0)
                 auscore2dollarsk_1
                 auscore2dollarsk_1
                 auscore2dollarsk_1)
              (* 69.0 auscore2dollarsk_1 auscore2dollarsk_1 buscore2dollarsk_3)
              (* (- 56.0)
                 auscore2dollarsk_1
                 buscore2dollarsk_3
                 buscore2dollarsk_3)
              (* 16.0 buscore2dollarsk_3 buscore2dollarsk_3 buscore2dollarsk_3)
              (* 32.0 auscore2dollarsk_1 auscore2dollarsk_1 ruscore2dollarsk_2)
              (* (- 47.0)
                 auscore2dollarsk_1
                 buscore2dollarsk_3
                 ruscore2dollarsk_2)
              (* 20.0 buscore2dollarsk_3 buscore2dollarsk_3 ruscore2dollarsk_2)
              (* (- 10.0)
                 auscore2dollarsk_1
                 ruscore2dollarsk_2
                 ruscore2dollarsk_2)
              (* 7.0 buscore2dollarsk_3 ruscore2dollarsk_2 ruscore2dollarsk_2)
              (* ruscore2dollarsk_2 ruscore2dollarsk_2 ruscore2dollarsk_2))
           0.0))
(assert (let ((a_1 (+ (* 5.0 ruscore2dollarsk_2)
                      (* (- 7.0) auscore2dollarsk_1)
                      (* 4.0 buscore2dollarsk_3))))
          (not (= (+ (* (- (/ 1.0 4.0)) guscore2dollarsk_0)
                     (* (- 31.0)
                        ruscore2dollarsk_2
                        ruscore2dollarsk_2
                        ruscore2dollarsk_2)
                     (* 69.0
                        auscore2dollarsk_1
                        ruscore2dollarsk_2
                        ruscore2dollarsk_2)
                     (* (- 56.0)
                        auscore2dollarsk_1
                        auscore2dollarsk_1
                        ruscore2dollarsk_2)
                     (* 16.0
                        auscore2dollarsk_1
                        auscore2dollarsk_1
                        auscore2dollarsk_1)
                     (* 32.0 ruscore2dollarsk_2 ruscore2dollarsk_2 a_1)
                     (* (- 47.0) auscore2dollarsk_1 ruscore2dollarsk_2 a_1)
                     (* 20.0 auscore2dollarsk_1 auscore2dollarsk_1 a_1)
                     (* (- 10.0) ruscore2dollarsk_2 a_1 a_1)
                     (* 7.0 auscore2dollarsk_1 a_1 a_1)
                     (* a_1 a_1 a_1))
                  0.0))))
(check-sat)
(exit)
