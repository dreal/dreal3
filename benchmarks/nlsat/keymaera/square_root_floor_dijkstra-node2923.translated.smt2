(set-logic QF_NRA)
(declare-fun huscore2dollarsk!1 () Real)
(declare-fun ruscore2dollarsk!0 () Real)
(declare-fun quscore2dollarsk!3 () Real)
(declare-fun r0 () Real)
(declare-fun q0 () Real)
(declare-fun p0 () Real)
(declare-fun puscore2dollarsk!2 () Real)
(assert (>= ruscore2dollarsk!0 huscore2dollarsk!1))
(assert (not (= quscore2dollarsk!3 1.0)))
(assert (= (* puscore2dollarsk!2 puscore2dollarsk!2 q0)
           (* quscore2dollarsk!3
              (+ (* p0 p0) (* q0 (+ (* (- 1.0) ruscore2dollarsk!0) r0))))))
(assert (not (= (* q0
                   (+ (* (/ 1.0 2.0) puscore2dollarsk!2)
                      (* (/ 1.0 4.0) quscore2dollarsk!3))
                   (+ (* (/ 1.0 2.0) puscore2dollarsk!2)
                      (* (/ 1.0 4.0) quscore2dollarsk!3)))
                (* (/ 1.0 4.0)
                   quscore2dollarsk!3
                   (+ (* p0 p0)
                      (* q0
                         (+ (* (- 1.0) ruscore2dollarsk!0)
                            puscore2dollarsk!2
                            (* (/ 1.0 4.0) quscore2dollarsk!3)
                            r0)))))))
(check-sat)
(exit)
