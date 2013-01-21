(set-logic QF_NRA)
(declare-fun auscore0dollarsk!5 () Real)
(declare-fun asuscore0dollarsk!4 () Real)
(declare-fun xuscore0dollarsk!3 () Real)
(declare-fun xsuscore0dollarsk!2 () Real)
(declare-fun yuscore0dollarsk!1 () Real)
(declare-fun ysuscore0dollarsk!0 () Real)
(assert (>= auscore0dollarsk!5 0.0))
(assert (>= asuscore0dollarsk!4 0.0))
(assert (>= xuscore0dollarsk!3 0.0))
(assert (>= xsuscore0dollarsk!2 0.0))
(assert (>= yuscore0dollarsk!1 0.0))
(assert (>= ysuscore0dollarsk!0 0.0))
(assert (not (>= (+ (* auscore0dollarsk!5
                       auscore0dollarsk!5
                       xsuscore0dollarsk!2
                       xsuscore0dollarsk!2)
                    (* auscore0dollarsk!5
                       auscore0dollarsk!5
                       ysuscore0dollarsk!0
                       ysuscore0dollarsk!0)
                    (* (- 2.0)
                       asuscore0dollarsk!4
                       auscore0dollarsk!5
                       xsuscore0dollarsk!2
                       xuscore0dollarsk!3)
                    (* (- 2.0)
                       asuscore0dollarsk!4
                       auscore0dollarsk!5
                       ysuscore0dollarsk!0
                       yuscore0dollarsk!1)
                    (* asuscore0dollarsk!4
                       asuscore0dollarsk!4
                       xuscore0dollarsk!3
                       xuscore0dollarsk!3)
                    (* asuscore0dollarsk!4
                       asuscore0dollarsk!4
                       yuscore0dollarsk!1
                       yuscore0dollarsk!1))
                 0.0)))
(check-sat)
(exit)
