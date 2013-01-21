(set-logic QF_NRA)
(declare-fun k () Real)
(declare-fun yuscore2dollarsk!1 () Real)
(declare-fun xuscore2dollarsk!0 () Real)
(assert (not (= yuscore2dollarsk!1 k)))
(assert (= (+ (* 12.0 xuscore2dollarsk!0)
              (* yuscore2dollarsk!1 yuscore2dollarsk!1)
              (* 6.0
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1))
           (+ (* 5.0
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1)
              (* 2.0
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1
                 yuscore2dollarsk!1))))
(assert (not (= (+ (* 12.0 xuscore2dollarsk!0)
                   (* 12.0
                      yuscore2dollarsk!1
                      yuscore2dollarsk!1
                      yuscore2dollarsk!1
                      yuscore2dollarsk!1
                      yuscore2dollarsk!1)
                   (* (+ 1.0 yuscore2dollarsk!1) (+ 1.0 yuscore2dollarsk!1))
                   (* 6.0
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)))
                (+ (* 5.0
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1))
                   (* 2.0
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1)
                      (+ 1.0 yuscore2dollarsk!1))))))
(check-sat)
(exit)
