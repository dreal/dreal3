(set-logic QF_NRA)
(declare-fun auscore0dollarsk_5 () Real)
(declare-fun asuscore0dollarsk_4 () Real)
(declare-fun xuscore0dollarsk_3 () Real)
(declare-fun xsuscore0dollarsk_2 () Real)
(declare-fun yuscore0dollarsk_1 () Real)
(declare-fun ysuscore0dollarsk_0 () Real)
(assert (>= auscore0dollarsk_5 0.0))
(assert (>= asuscore0dollarsk_4 0.0))
(assert (>= xuscore0dollarsk_3 0.0))
(assert (>= xsuscore0dollarsk_2 0.0))
(assert (>= yuscore0dollarsk_1 0.0))
(assert (>= ysuscore0dollarsk_0 0.0))
(assert (not (>= (+ (* auscore0dollarsk_5
                       auscore0dollarsk_5
                       xsuscore0dollarsk_2
                       xsuscore0dollarsk_2)
                    (* auscore0dollarsk_5
                       auscore0dollarsk_5
                       ysuscore0dollarsk_0
                       ysuscore0dollarsk_0)
                    (* (- 2.0)
                       asuscore0dollarsk_4
                       auscore0dollarsk_5
                       xsuscore0dollarsk_2
                       xuscore0dollarsk_3)
                    (* (- 2.0)
                       asuscore0dollarsk_4
                       auscore0dollarsk_5
                       ysuscore0dollarsk_0
                       yuscore0dollarsk_1)
                    (* asuscore0dollarsk_4
                       asuscore0dollarsk_4
                       xuscore0dollarsk_3
                       xuscore0dollarsk_3)
                    (* asuscore0dollarsk_4
                       asuscore0dollarsk_4
                       yuscore0dollarsk_1
                       yuscore0dollarsk_1))
                 0.0)))
(check-sat)
(exit)
