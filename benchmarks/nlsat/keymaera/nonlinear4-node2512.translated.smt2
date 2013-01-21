(set-logic QF_NRA)
(declare-fun x1uscore1dollarsk!0 () Real)
(declare-fun x2uscore1dollarsk!1 () Real)
(declare-fun a () Real)
(declare-fun x2 () Real)
(declare-fun x1 () Real)
(assert (>= x1uscore1dollarsk!0 0.0))
(assert (>= x2uscore1dollarsk!1 0.0))
(assert (>= (+ (* (/ 1.0 2.0) x1 x1) (* (- (/ 1.0 2.0)) x2 x2)) a))
(assert (not (>= (+ (* (- 1.0)
                       x2uscore1dollarsk!1
                       (+ (* (- 1.0) x1uscore1dollarsk!0)
                          (* x1uscore1dollarsk!0
                             x1uscore1dollarsk!0
                             x2uscore1dollarsk!1)))
                    (* x1uscore1dollarsk!0
                       (+ x2uscore1dollarsk!1
                          (* x1uscore1dollarsk!0
                             x2uscore1dollarsk!1
                             x2uscore1dollarsk!1))))
                 0.0)))
(check-sat)
(exit)
