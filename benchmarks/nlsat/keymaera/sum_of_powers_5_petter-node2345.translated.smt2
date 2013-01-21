(set-logic QF_NRA)
(declare-fun k () Real)
(declare-fun yuscore2dollarsk_1 () Real)
(declare-fun xuscore2dollarsk_0 () Real)
(assert (not (= yuscore2dollarsk_1 k)))
(assert (= (+ (* 12.0 xuscore2dollarsk_0)
              (* yuscore2dollarsk_1 yuscore2dollarsk_1)
              (* 6.0
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1))
           (+ (* 5.0
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1)
              (* 2.0
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1
                 yuscore2dollarsk_1))))
(assert (not (= (+ (* 12.0 xuscore2dollarsk_0)
                   (* 12.0
                      yuscore2dollarsk_1
                      yuscore2dollarsk_1
                      yuscore2dollarsk_1
                      yuscore2dollarsk_1
                      yuscore2dollarsk_1)
                   (* (+ 1.0 yuscore2dollarsk_1) (+ 1.0 yuscore2dollarsk_1))
                   (* 6.0
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)))
                (+ (* 5.0
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1))
                   (* 2.0
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1)
                      (+ 1.0 yuscore2dollarsk_1))))))
(check-sat)
(exit)
